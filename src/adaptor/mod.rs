use crate::host::ExternalHostCallEntry;
use crate::host::ForeignInst;
use crate::utils::field_to_bn;
use halo2_proofs::arithmetic::{BaseExt, FieldExt};
use num_bigint::BigUint;

// pub mod bls381adaptor;
pub mod bn256adaptor;
pub mod hashadaptor;
pub mod keccakadaptor;
pub mod merkleadaptor;
pub mod msmadaptor;

pub fn get_max_round(k: usize, reference_max: usize) -> usize {
    if k >= 22 {
        reference_max << (k - 22)
    } else {
        // we do not support host when k < 22
        0
    }
}

pub fn fr_to_args<F: BaseExt>(
    f: F,
    nblimbs: usize,
    sz: usize,
    op: ForeignInst,
) -> Vec<ExternalHostCallEntry> {
    let mut bn = field_to_bn(&f);
    let mut ret = vec![];
    for _ in 0..nblimbs {
        let d: BigUint = BigUint::from(1u128 << sz);
        let r = bn.clone() % d.clone();
        let value = if r == BigUint::from(0 as u32) {
            0 as u64
        } else {
            r.to_u64_digits()[0]
        };
        bn = bn / d;
        let entry = ExternalHostCallEntry {
            op: op as usize,
            value,
            is_ret: false,
        };
        ret.append(&mut vec![entry]);
    }
    ret
}

pub fn get_selected_entries<Fr: FieldExt>(
    shared_operands: &Vec<Fr>,
    shared_opcodes: &Vec<Fr>,
    opcodes: &Vec<Fr>,
) -> Vec<((Fr, Fr), Fr)> {
    let entries = shared_operands
        .clone()
        .into_iter()
        .zip(shared_opcodes.clone());

    let v = entries
        .filter(|(_operand, opcode)| opcodes.contains(opcode))
        .collect::<Vec<(Fr, Fr)>>();

    let len = v.len();

    let shared_index: Vec<Fr> = v
        .iter()
        .enumerate()
        .map(|(i, _)| Fr::from((len - i) as u64))
        .collect();

    v.into_iter()
        .zip(shared_index)
        .collect::<Vec<((Fr, Fr), Fr)>>()
}

#[cfg(test)]
mod tests {
    use super::get_selected_entries;
    use crate::utils::field_to_u64;
    use halo2_proofs::pairing::bn256::Fr;

    #[test]
    fn filter_single_opcode_assigns_descending_indices() {
        let shared_operands = vec![
            Fr::from(10u64),
            Fr::from(11u64),
            Fr::from(12u64),
            Fr::from(13u64),
        ];
        let shared_opcodes = vec![
            Fr::from(1u64),
            Fr::from(2u64),
            Fr::from(3u64),
            Fr::from(2u64),
        ];
        let opcodes = vec![Fr::from(2u64)];
        let selected = get_selected_entries(&shared_operands, &shared_opcodes, &opcodes);
        assert_eq!(selected.len(), 2);
        assert_eq!(selected[0].0 .0, Fr::from(11u64));
        assert_eq!(selected[0].0 .1, Fr::from(2u64));
        assert_eq!(field_to_u64(&selected[0].1), 2);
        assert_eq!(field_to_u64(&selected[1].1), 1);
    }

    #[test]
    fn filter_mixed_opcodes_preserves_order() {
        let shared_operands = vec![Fr::from(21u64), Fr::from(22u64), Fr::from(23u64)];
        let shared_opcodes = vec![Fr::from(5u64), Fr::from(7u64), Fr::from(5u64)];
        let opcodes = vec![Fr::from(5u64), Fr::from(7u64)];
        let selected = get_selected_entries(&shared_operands, &shared_opcodes, &opcodes);
        assert_eq!(selected.len(), 3);
        assert_eq!(selected[0].0 .0, Fr::from(21u64));
        assert_eq!(selected[1].0 .0, Fr::from(22u64));
        assert_eq!(selected[2].0 .0, Fr::from(23u64));
        assert_eq!(field_to_u64(&selected[0].1), 3);
        assert_eq!(field_to_u64(&selected[1].1), 2);
        assert_eq!(field_to_u64(&selected[2].1), 1);
    }
}
