use crate::circuits::{LookupAssistChip, LookupAssistConfig};
use crate::utils::{GateCell, Limb};
use crate::{
    customized_circuits, customized_circuits_expand, item_count, table_item, value_for_assign,
};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::Region,
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, Selector, VirtualCells},
    poly::Rotation,
};
use std::marker::PhantomData;

pub const BIT_XOR: u8 = 1;
pub const BIT_AND: u8 = 2;
pub const BIT_NOT_AND: u8 = 3;
pub const BIT_ROTATE_LEFT: u8 = 4; // 4 + 7, max 11 ---- total 2^4
pub const BIT_ROTATE_RIGHT: u8 = 12; // 12 + 7, max 21 -- total 2^5

// a0 a1 a2 a3
// a4 a5 a6 a7
// b0 b1 b2 b3
// b4 b5 b6 b7
// c0 c1 c2 c3
// c4 c5 c6 c7
// (a0,b0,c0) in lookup_set

#[rustfmt::skip]
customized_circuits!(BitsArithConfig, 1, 0, 4, 0,
   | lhs   |  rhs   |  res   | op
);

impl LookupAssistConfig for BitsArithConfig {
    /// register columns (col) to be XOR checked by limb size (sz)
    fn register<F: FieldExt>(
        &self,
        cs: &mut ConstraintSystem<F>,
        cols: impl Fn(&mut VirtualCells<F>) -> Vec<Expression<F>>,
    ) {
        for i in 0..4 {
            cs.lookup_any("check bits arith", |meta| {
                let lhs = self.get_expr(meta, BitsArithConfig::lhs());
                let rhs = self.get_expr(meta, BitsArithConfig::rhs());
                let op = self.get_expr(meta, BitsArithConfig::op());
                let res = self.get_expr(meta, BitsArithConfig::res());
                let icols = cols(meta);
                vec![
                    (icols[i].clone(), lhs),
                    (icols[i + 4].clone(), rhs),
                    (icols[i + 8].clone(), res),
                    (icols[12].clone(), op),
                ]
            });
        }
    }
}

pub struct BitsArithChip<F: FieldExt> {
    config: BitsArithConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> LookupAssistChip<F> for BitsArithChip<F> {
    fn provide_lookup_evidence(
        &mut self,
        _region: &Region<F>,
        _value: F,
        _sz: u64,
    ) -> Result<(), Error> {
        Ok(())
    }
}

impl<F: FieldExt> BitsArithChip<F> {
    pub fn new(config: BitsArithConfig) -> Self {
        BitsArithChip {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(cs: &mut ConstraintSystem<F>) -> BitsArithConfig {
        let fixed = [0; 4].map(|_| cs.fixed_column());
        let selector = [];

        let config = BitsArithConfig {
            fixed,
            selector,
            witness: [],
        };

        config
    }

    fn assign_table_entries(
        &mut self,
        region: &Region<F>,
        opcall: impl Fn(u8, u8) -> u8,
        opcode: u8,
        offset: &mut usize,
    ) -> Result<(), Error> {
        let op = F::from(opcode as u64);
        for i in 0..=u8::MAX {
            for j in 0..=u8::MAX {
                let lhs = F::from(i as u64);
                let rhs = F::from(j as u64);
                let res = F::from(opcall(i, j) as u64);
                self.config
                    .assign_cell(region, *offset, &BitsArithConfig::lhs(), lhs)?;
                self.config
                    .assign_cell(region, *offset, &BitsArithConfig::rhs(), rhs)?;
                self.config
                    .assign_cell(region, *offset, &BitsArithConfig::res(), res)?;
                self.config
                    .assign_cell(region, *offset, &BitsArithConfig::op(), op)?;
                *offset = *offset + 1;
            }
        }
        Ok(())
    }

    /// initialize the table columns that contains every possible result of 8-bit value via XOR or ADD operation
    /// initialize needs to be called before using the BitsArithchip
    pub fn initialize(&mut self, region: &Region<F>, offset: &mut usize) -> Result<(), Error> {
        // initialize the XOR table with the encoded value
        self.assign_table_entries(region, |x, y| x ^ y, BIT_XOR, offset)?;
        self.assign_table_entries(region, |x, y| x & y, BIT_AND, offset)?;
        self.assign_table_entries(region, |x, y| (!x) & y, BIT_NOT_AND, offset)?;
        for i in 0..8 {
            self.assign_table_entries(
                region,
                |x, y| {
                    if i != 0 {
                        ((x << i) & 0xff) + (y >> (8 - i))
                    } else {
                        x
                    }
                },
                BIT_ROTATE_LEFT + i,
                offset,
            )?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{BitsArithChip, BitsArithConfig, BIT_AND, BIT_XOR};
    use crate::circuits::LookupAssistConfig;
    use crate::value_for_assign;
    use halo2_proofs::circuit::floor_planner::FlatFloorPlanner;
    use halo2_proofs::dev::MockProver;
    use halo2_proofs::pairing::bn256::Fr;
    use halo2_proofs::{
        circuit::{Chip, Layouter, Region},
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, VirtualCells},
        poly::Rotation,
    };

    #[derive(Clone, Debug)]
    struct HelperChipConfig {
        cols: [Column<Advice>; 13],
    }

    impl HelperChipConfig {
        fn lookup_cols(&self, cs: &mut VirtualCells<Fr>) -> Vec<Expression<Fr>> {
            self.cols
                .iter()
                .map(|col| cs.query_advice(*col, Rotation::cur()))
                .collect()
        }
    }

    #[derive(Clone, Debug)]
    struct HelperChip {
        config: HelperChipConfig,
    }

    impl Chip<Fr> for HelperChip {
        type Config = HelperChipConfig;
        type Loaded = ();

        fn config(&self) -> &Self::Config {
            &self.config
        }

        fn loaded(&self) -> &Self::Loaded {
            &()
        }
    }

    impl HelperChip {
        fn new(config: HelperChipConfig) -> Self {
            HelperChip { config }
        }

        fn configure(cs: &mut ConstraintSystem<Fr>) -> HelperChipConfig {
            let cols = [0; 13].map(|_| cs.advice_column());
            cols.map(|c| cs.enable_equality(c));
            HelperChipConfig { cols }
        }

        fn assign_row(
            &self,
            region: &Region<Fr>,
            offset: usize,
            values: [Fr; 13],
        ) -> Result<(), Error> {
            for (idx, value) in values.iter().enumerate() {
                region.assign_advice(
                    || "bits arith input",
                    self.config.cols[idx],
                    offset,
                    || value_for_assign!(*value),
                )?;
            }
            Ok(())
        }
    }

    #[derive(Clone, Debug)]
    struct TestCircuit {
        lhs: [u8; 4],
        rhs: [u8; 4],
        op: u8,
        res: [u8; 4],
    }

    impl Circuit<Fr> for TestCircuit {
        type Config = (BitsArithConfig, HelperChipConfig);
        type FloorPlanner = FlatFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self {
                lhs: [0; 4],
                rhs: [0; 4],
                op: BIT_XOR,
                res: [0; 4],
            }
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            let bits_config = BitsArithChip::<Fr>::configure(meta);
            let helper_config = HelperChip::configure(meta);
            bits_config.register(meta, |c| helper_config.lookup_cols(c));
            (bits_config, helper_config)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let helper = HelperChip::new(config.1);
            layouter.assign_region(
                || "bits arith test",
                |region| {
                    let mut offset = 0;
                    let mut bits_chip = BitsArithChip::<Fr>::new(config.0.clone());
                    bits_chip.initialize(&region, &mut offset)?;

                    let mut values = [Fr::zero(); 13];
                    for i in 0..4 {
                        values[i] = Fr::from(self.lhs[i] as u64);
                        values[i + 4] = Fr::from(self.rhs[i] as u64);
                        values[i + 8] = Fr::from(self.res[i] as u64);
                    }
                    values[12] = Fr::from(self.op as u64);
                    helper.assign_row(&region, 0, values)?;
                    Ok(())
                },
            )?;
            Ok(())
        }
    }

    #[test]
    fn test_bits_arith_xor() {
        let lhs = [0x0f, 0x12, 0x55, 0xaa];
        let rhs = [0xf0, 0x34, 0xaa, 0x0f];
        let res = [
            lhs[0] ^ rhs[0],
            lhs[1] ^ rhs[1],
            lhs[2] ^ rhs[2],
            lhs[3] ^ rhs[3],
        ];
        let circuit = TestCircuit {
            lhs,
            rhs,
            op: BIT_XOR,
            res,
        };
        let prover = MockProver::run(18, &circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn test_bits_arith_and() {
        let lhs = [0xf0, 0x3c, 0x55, 0xaa];
        let rhs = [0x0f, 0x0f, 0xaa, 0x0f];
        let res = [
            lhs[0] & rhs[0],
            lhs[1] & rhs[1],
            lhs[2] & rhs[2],
            lhs[3] & rhs[3],
        ];
        let circuit = TestCircuit {
            lhs,
            rhs,
            op: BIT_AND,
            res,
        };
        let prover = MockProver::run(18, &circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
}
