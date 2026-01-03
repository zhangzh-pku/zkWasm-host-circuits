#[cfg(test)]
mod tests {
    use crate::host::{ExternalHostCallEntry, ExternalHostCallEntryTable, ForeignInst};
    use crate::proof::build_host_circuit;
    use crate::circuits::bn256::{Bn256PairChip, Bn256SumChip};
    use crate::utils::field_to_bn;
    use ff::Field;
    use halo2_proofs::arithmetic::FieldExt;
    use halo2_proofs::dev::MockProver;
    use halo2_proofs::pairing::bn256::pairing;
    use halo2_proofs::pairing::bn256::Fr;
    use halo2_proofs::pairing::bn256::{Fq as Bn256Fq, G1Affine, G2Affine, Gt as Bn256Gt, G1, G2};
    use halo2_proofs::pairing::group::Group;
    use num_bigint::BigUint;
    use rand::rngs::OsRng;
    use std::fs::File;
    use std::ops::Add;

    fn limbs_to_bn(entries: &[ExternalHostCallEntry], limb_bits: u64) -> BigUint {
        let mut acc = BigUint::from(0u64);
        let base = BigUint::from(1u128 << limb_bits);
        for (idx, entry) in entries.iter().enumerate() {
            let term = BigUint::from(entry.value) * base.pow(idx as u32);
            acc += term;
        }
        acc
    }

    fn split_u108(mut value: BigUint, limbs: usize) -> Vec<BigUint> {
        let base: BigUint = BigUint::from(1u128) << 108;
        let mut out = Vec::with_capacity(limbs);
        for _ in 0..limbs {
            out.push(&value % &base);
            value /= &base;
        }
        out
    }

    fn bn256_fr_to_args(f: Fr, op: ForeignInst) -> Vec<ExternalHostCallEntry> {
        let mut bn = field_to_bn(&f);
        let mut ret = vec![];
        for _ in 0..4 {
            let d: BigUint = BigUint::from(1u128 << 64);
            let r = bn.clone() % d.clone();
            let value = if r == BigUint::from(0 as u32) {
                0 as u64
            } else {
                r.to_u64_digits()[0]
            };
            println!("d is {:?}, remainder is {:?}", d, r);
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

    fn bn256_fq_to_args(f: Bn256Fq, op: ForeignInst) -> Vec<ExternalHostCallEntry> {
        let mut bn = field_to_bn(&f);
        let mut ret = vec![];
        for _ in 0..5 {
            let d: BigUint = BigUint::from(1u64 << 54);
            let r = bn.clone() % d.clone();
            let value = if r == BigUint::from(0 as u32) {
                0 as u64
            } else {
                r.to_u64_digits()[0]
            };
            println!("d is {:?}, remainder is {:?}", d, r);
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

    fn bn256_gt_to_pair_args(f: Bn256Gt) -> Vec<ExternalHostCallEntry> {
        let c000 = bn256_fq_to_args(f.0.c0.c0.c0, ForeignInst::Bn254PairG3);
        let c001 = bn256_fq_to_args(f.0.c0.c0.c1, ForeignInst::Bn254PairG3);
        let c010 = bn256_fq_to_args(f.0.c0.c1.c0, ForeignInst::Bn254PairG3);
        let c011 = bn256_fq_to_args(f.0.c0.c1.c1, ForeignInst::Bn254PairG3);
        let c020 = bn256_fq_to_args(f.0.c0.c2.c0, ForeignInst::Bn254PairG3);
        let c021 = bn256_fq_to_args(f.0.c0.c2.c1, ForeignInst::Bn254PairG3);
        let c100 = bn256_fq_to_args(f.0.c1.c0.c0, ForeignInst::Bn254PairG3);
        let c101 = bn256_fq_to_args(f.0.c1.c0.c1, ForeignInst::Bn254PairG3);
        let c110 = bn256_fq_to_args(f.0.c1.c1.c0, ForeignInst::Bn254PairG3);
        let c111 = bn256_fq_to_args(f.0.c1.c1.c1, ForeignInst::Bn254PairG3);
        let c120 = bn256_fq_to_args(f.0.c1.c2.c0, ForeignInst::Bn254PairG3);
        let c121 = bn256_fq_to_args(f.0.c1.c2.c1, ForeignInst::Bn254PairG3);
        vec![
            c000, c001, c010, c011, c020, c021, c100, c101, c110, c111, c120, c121,
        ]
        .into_iter()
        .flatten()
        .collect()
    }

    fn bn256_g1_to_args(g: G1, op: ForeignInst) -> Vec<ExternalHostCallEntry> {
        let g_af = G1Affine::from(g);
        let mut a = bn256_fq_to_args(g_af.x, op);
        let mut b = bn256_fq_to_args(g_af.y, op);
        let z: u64 = g.is_identity().unwrap_u8() as u64;
        a.append(&mut b);
        a.append(&mut vec![ExternalHostCallEntry {
            op: op as usize,
            value: z,
            is_ret: false,
        }]);
        a
    }

    fn bn256_g2_to_pair_args(g: G2) -> Vec<ExternalHostCallEntry> {
        let g_af = G2Affine::from(g);
        let x0 = bn256_fq_to_args(g_af.x.c0, ForeignInst::Bn254PairG2);
        let x1 = bn256_fq_to_args(g_af.x.c1, ForeignInst::Bn254PairG2);
        let y0 = bn256_fq_to_args(g_af.y.c0, ForeignInst::Bn254PairG2);
        let y1 = bn256_fq_to_args(g_af.y.c1, ForeignInst::Bn254PairG2);
        let z: u64 = g.is_identity().unwrap_u8() as u64;
        let zentry = ExternalHostCallEntry {
            op: ForeignInst::Bn254PairG2 as usize,
            value: z,
            is_ret: false,
        };
        vec![x0, x1, y0, y1, vec![zentry]]
            .into_iter()
            .flatten()
            .collect()
    }

    fn create_bn256_pair_shared_table(a: G1, b: G2) -> ExternalHostCallEntryTable {
        let a_af = G1Affine::from(a);
        let b_af = G2Affine::from(b);
        let ab: Bn256Gt = pairing(&a_af, &b_af);
        let g1_args = bn256_g1_to_args(a, ForeignInst::Bn254PairG1);
        let g2_args = bn256_g2_to_pair_args(b);
        let ab_args = bn256_gt_to_pair_args(ab);
        let table = ExternalHostCallEntryTable(
            vec![g1_args, g2_args, ab_args]
                .into_iter()
                .flatten()
                .collect(),
        );
        table
    }

    fn create_bn256_sum_input(new: u32, a: Fr, g: G1, sum: G1) -> Vec<ExternalHostCallEntry> {
        let mut r = vec![];
        r.append(&mut vec![ExternalHostCallEntry {
            op: ForeignInst::Bn254SumNew as usize,
            value: new as u64,
            is_ret: false,
        }]);
        r.append(&mut bn256_fr_to_args(a, ForeignInst::Bn254SumScalar));
        r.append(&mut bn256_g1_to_args(g, ForeignInst::Bn254SumG1));
        r.append(&mut bn256_g1_to_args(sum, ForeignInst::Bn254SumResult));
        r
    }
    #[test]
    fn generate_bn256_pair_input() {
        let a = G1::random(&mut OsRng);
        let b = G2::random(&mut OsRng);
        let table = create_bn256_pair_shared_table(a, b);
        let entries = &table.0;
        let g1_len = 5usize + 5 + 1;
        let g2_len = 5usize + 5 + 5 + 5 + 1;
        let gt_len = 12usize * 5;
        assert_eq!(entries.len(), g1_len + g2_len + gt_len);
        assert!(entries[..g1_len]
            .iter()
            .all(|entry| entry.op == ForeignInst::Bn254PairG1 as usize));
        assert!(entries[g1_len..g1_len + g2_len]
            .iter()
            .all(|entry| entry.op == ForeignInst::Bn254PairG2 as usize));
        assert!(entries[g1_len + g2_len..]
            .iter()
            .all(|entry| entry.op == ForeignInst::Bn254PairG3 as usize));
        let file = File::create("bn256pairtest.json").expect("can not create file");
        serde_json::to_writer_pretty(file, &table).expect("can not write to file");
    }

    #[test]
    fn generate_bn256_sum_input() {
        let l = [2usize, 4, 3];
        let mut inputs = vec![];
        for i in 0..3 {
            let mut z = G1::identity();
            for j in 0..l[i] {
                let new = if j == 0 { 1 } else { 0 };
                let a_j = Fr::random(&mut OsRng);
                let g_j = G1::random(&mut OsRng);
                let r = g_j * a_j;
                z = z.add(r.clone());
                inputs.append(&mut create_bn256_sum_input(new, a_j, g_j, z));
            }
        }
        let table = ExternalHostCallEntryTable(inputs);
        let entries = &table.0;
        let step_len = 1usize + 4 + 11 + 11;
        let total_steps: usize = l.iter().sum();
        assert_eq!(entries.len(), step_len * total_steps);
        let mut expected_new_flags = Vec::with_capacity(total_steps);
        for count in l {
            for step in 0..count {
                expected_new_flags.push(if step == 0 { 1u64 } else { 0u64 });
            }
        }
        for (idx, chunk) in entries.chunks(step_len).enumerate() {
            assert_eq!(chunk[0].op, ForeignInst::Bn254SumNew as usize);
            assert_eq!(chunk[0].value, expected_new_flags[idx]);
            assert!(chunk[1..5]
                .iter()
                .all(|entry| entry.op == ForeignInst::Bn254SumScalar as usize));
            assert!(chunk[5..16]
                .iter()
                .all(|entry| entry.op == ForeignInst::Bn254SumG1 as usize));
            assert!(chunk[16..]
                .iter()
                .all(|entry| entry.op == ForeignInst::Bn254SumResult as usize));
        }
        let file = File::create("bn256sumtest.json").expect("can not create file");
        serde_json::to_writer_pretty(file, &table).expect("can not write to file");
    }

    #[test]
    fn bn256_pair_host_circuit_accepts_valid_pairing() {
        let a = G1::generator();
        let b = G2::generator();
        let table = create_bn256_pair_shared_table(a, b);
        let a_af = G1Affine::from(a);
        let b_af = G2Affine::from(b);
        let gt = pairing(&a_af, &b_af);
        let g1_x = limbs_to_bn(&table.0[0..5], 54);
        let g1_y = limbs_to_bn(&table.0[5..10], 54);
        assert_eq!(g1_x, field_to_bn(&a_af.x));
        assert_eq!(g1_y, field_to_bn(&a_af.y));
        let g1_x_limbs = split_u108(g1_x.clone(), 3);
        let g1_y_limbs = split_u108(g1_y.clone(), 3);
        let g1_x_m0 = limbs_to_bn(&table.0[0..2], 54);
        let g1_x_m1 = limbs_to_bn(&table.0[2..4], 54);
        let g1_x_m2 = limbs_to_bn(&table.0[4..5], 54);
        assert_eq!(g1_x_limbs[0], g1_x_m0);
        assert_eq!(g1_x_limbs[1], g1_x_m1);
        assert_eq!(g1_x_limbs[2], g1_x_m2);
        let g1_y_m0 = limbs_to_bn(&table.0[5..7], 54);
        let g1_y_m1 = limbs_to_bn(&table.0[7..9], 54);
        let g1_y_m2 = limbs_to_bn(&table.0[9..10], 54);
        assert_eq!(g1_y_limbs[0], g1_y_m0);
        assert_eq!(g1_y_limbs[1], g1_y_m1);
        assert_eq!(g1_y_limbs[2], g1_y_m2);
        let g2_x0 = limbs_to_bn(&table.0[11..16], 54);
        let g2_x1 = limbs_to_bn(&table.0[16..21], 54);
        let g2_y0 = limbs_to_bn(&table.0[21..26], 54);
        let g2_y1 = limbs_to_bn(&table.0[26..31], 54);
        assert_eq!(g2_x0, field_to_bn(&b_af.x.c0));
        assert_eq!(g2_x1, field_to_bn(&b_af.x.c1));
        assert_eq!(g2_y0, field_to_bn(&b_af.y.c0));
        assert_eq!(g2_y1, field_to_bn(&b_af.y.c1));
        let gt_c000 = limbs_to_bn(&table.0[32..37], 54);
        assert_eq!(gt_c000, field_to_bn(&gt.0.c0.c0.c0));
        let circuit = build_host_circuit::<Bn256PairChip<Fr>>(&table, 23, ());
        let prover = MockProver::run(23, &circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    #[ignore = "halo2ecc rejects identity points"]
    fn bn256_pair_host_circuit_accepts_identity_g1() {
        let a = G1::identity();
        let b = G2::generator();
        let table = create_bn256_pair_shared_table(a, b);
        let circuit = build_host_circuit::<Bn256PairChip<Fr>>(&table, 23, ());
        let prover = MockProver::run(23, &circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    #[ignore = "halo2ecc rejects identity points"]
    fn bn256_pair_host_circuit_accepts_identity_g2() {
        let a = G1::generator();
        let b = G2::identity();
        let table = create_bn256_pair_shared_table(a, b);
        let circuit = build_host_circuit::<Bn256PairChip<Fr>>(&table, 23, ());
        let prover = MockProver::run(23, &circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn bn256_pairing_bilinearity_scalar_commutes() {
        let p = G1::generator();
        let q = G2::generator();
        let a = Fr::random(&mut OsRng);
        let ap = p * a;
        let aq = q * a;
        let left = pairing(&G1Affine::from(ap), &G2Affine::from(q));
        let right = pairing(&G1Affine::from(p), &G2Affine::from(aq));
        assert_eq!(left, right);
    }

    #[test]
    fn bn256_pair_host_circuit_accepts_random_points() {
        let a = G1::random(&mut OsRng);
        let b = G2::random(&mut OsRng);
        let table = create_bn256_pair_shared_table(a, b);
        let circuit = build_host_circuit::<Bn256PairChip<Fr>>(&table, 23, ());
        let prover = MockProver::run(23, &circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn bn256_sum_host_circuit_accepts_single_step() {
        let g = G1::generator();
        let a = Fr::from(7u64);
        let sum = g * a;
        let entries = create_bn256_sum_input(1, a, g, sum);
        let table = ExternalHostCallEntryTable(entries);
        let circuit = build_host_circuit::<Bn256SumChip<Fr>>(&table, 23, ());
        let prover = MockProver::run(23, &circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn bn256_sum_scalar_zero() {
        let g = G1::generator();
        let a = Fr::zero();
        let sum = G1::identity();
        let entries = create_bn256_sum_input(1, a, g, sum);
        let table = ExternalHostCallEntryTable(entries);
        let circuit = build_host_circuit::<Bn256SumChip<Fr>>(&table, 23, ());
        let prover = MockProver::run(23, &circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn bn256_sum_scalar_one() {
        let g = G1::generator();
        let a = Fr::one();
        let sum = g * a;
        let entries = create_bn256_sum_input(1, a, g, sum);
        let table = ExternalHostCallEntryTable(entries);
        let circuit = build_host_circuit::<Bn256SumChip<Fr>>(&table, 23, ());
        let prover = MockProver::run(23, &circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn bn256_sum_multiple_steps() {
        let mut entries = Vec::new();
        let mut acc = G1::identity();
        let steps = [
            (Fr::from(3u64), G1::random(&mut OsRng)),
            (Fr::from(5u64), G1::random(&mut OsRng)),
            (Fr::from(7u64), G1::random(&mut OsRng)),
        ];
        for (idx, (scalar, point)) in steps.iter().enumerate() {
            let new = if idx == 0 { 1 } else { 0 };
            let term = point.clone() * *scalar;
            acc = acc.add(term);
            entries.append(&mut create_bn256_sum_input(new, *scalar, point.clone(), acc));
        }
        let table = ExternalHostCallEntryTable(entries);
        let circuit = build_host_circuit::<Bn256SumChip<Fr>>(&table, 23, ());
        let prover = MockProver::run(23, &circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn bn256_sum_interleaved_new_flags() {
        let mut entries = Vec::new();
        let mut acc = G1::identity();
        let points = [
            (Fr::from(2u64), G1::random(&mut OsRng), 1u32),
            (Fr::from(4u64), G1::random(&mut OsRng), 0u32),
            (Fr::from(6u64), G1::random(&mut OsRng), 0u32),
            (Fr::from(3u64), G1::random(&mut OsRng), 1u32),
            (Fr::from(9u64), G1::random(&mut OsRng), 0u32),
        ];
        for (scalar, point, new_flag) in points {
            if new_flag == 1 {
                acc = G1::identity();
            }
            acc = acc.add(point * scalar);
            entries.append(&mut create_bn256_sum_input(new_flag, scalar, point, acc));
        }
        let table = ExternalHostCallEntryTable(entries);
        let circuit = build_host_circuit::<Bn256SumChip<Fr>>(&table, 23, ());
        let prover = MockProver::run(23, &circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn bn256_sum_large_scalar() {
        let g = G1::random(&mut OsRng);
        let a = Fr::from_u128(u128::MAX);
        let sum = g * a;
        let entries = create_bn256_sum_input(1, a, g, sum);
        let table = ExternalHostCallEntryTable(entries);
        let circuit = build_host_circuit::<Bn256SumChip<Fr>>(&table, 23, ());
        let prover = MockProver::run(23, &circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn bn256_fr_limb_decomposition_round_trip() {
        let value = Fr::random(&mut OsRng);
        let entries = bn256_fr_to_args(value, ForeignInst::Bn254SumScalar);
        let reconstructed = limbs_to_bn(&entries, 64);
        assert_eq!(reconstructed, field_to_bn(&value));
    }

    #[test]
    fn bn256_fq_limb_decomposition_round_trip() {
        let value = Bn256Fq::random(&mut OsRng);
        let entries = bn256_fq_to_args(value, ForeignInst::Bn254PairG1);
        let reconstructed = limbs_to_bn(&entries, 54);
        assert_eq!(reconstructed, field_to_bn(&value));
    }

    #[test]
    fn bn256_u108_limb_reconstruction() {
        let original = BigUint::from(1u128 << 107) + BigUint::from(123u64);
        let limbs = split_u108(original.clone(), 3);
        let mut acc = BigUint::from(0u64);
        let base: BigUint = BigUint::from(1u128) << 108;
        for (idx, limb) in limbs.iter().enumerate() {
            acc += limb * base.pow(idx as u32);
        }
        assert_eq!(acc, original);
    }
}
