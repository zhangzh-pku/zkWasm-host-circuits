use halo2_proofs::pairing::bn256::Fr;
use poseidon::Poseidon;
use poseidon::Spec;
use std::cell::RefCell;

pub const PREFIX_CHALLENGE: u64 = 0u64;
pub const PREFIX_POINT: u64 = 1u64;
pub const PREFIX_SCALAR: u64 = 2u64;

// We have two hasher here
// 1. MERKLE_HASHER that is used for non sponge hash for hash two merkle siblings
// 2. POSEIDON_HASHER thas is use for poseidon hash of data
lazy_static::lazy_static! {
    pub static ref POSEIDON_HASHER: poseidon::Poseidon<Fr, 9, 8> = Poseidon::<Fr, 9, 8>::new(8, 63);
    pub static ref MERKLE_HASHER: poseidon::Poseidon<Fr, 3, 2> = Poseidon::<Fr, 3, 2>::new(8, 57);
    pub static ref MERKLE_LEAF_HASHER: poseidon::Poseidon<Fr, 3, 2> = Poseidon::<Fr, 3, 2>::new(8, 57);
    pub static ref POSEIDON_HASHER_SPEC: poseidon::Spec<Fr, 9, 8> = Spec::new(8, 63);
    pub static ref MERKLE_HASHER_SPEC: poseidon::Spec<Fr, 3, 2> = Spec::new(8, 57);
    pub static ref MERKLE_LEAF_HASHER_SPEC: poseidon::Spec<Fr, 3, 2> = Spec::new(8, 57);
}

thread_local! {
    static MERKLE_HASHER_LOCAL: RefCell<Poseidon<Fr, 3, 2>> =
        RefCell::new(MERKLE_HASHER.clone());
    static MERKLE_LEAF_HASHER_LOCAL: RefCell<Poseidon<Fr, 3, 2>> =
        RefCell::new(MERKLE_LEAF_HASHER.clone());
}

pub fn with_merkle_hasher<T>(f: impl FnOnce(&mut Poseidon<Fr, 3, 2>) -> T) -> T {
    MERKLE_HASHER_LOCAL.with(|hasher| {
        let mut hasher = hasher.borrow_mut();
        hasher.reset();
        f(&mut hasher)
    })
}

pub fn with_merkle_leaf_hasher<T>(f: impl FnOnce(&mut Poseidon<Fr, 3, 2>) -> T) -> T {
    MERKLE_LEAF_HASHER_LOCAL.with(|hasher| {
        let mut hasher = hasher.borrow_mut();
        hasher.reset();
        f(&mut hasher)
    })
}

#[cfg(test)]
mod tests {
    use ff::PrimeField;
    use halo2_proofs::pairing::bn256::Fr;
    use std::thread;
    #[test]
    fn test_poseidon() {
        const ZERO_HASHER_SQUEEZE: &str =
            "0x03f943aabd67cd7b72a539f3de686c3280c36c572be09f2b9193f5ef78761c6b"; //force the hasher is for fr field result.
        let mut hasher = super::POSEIDON_HASHER.clone();
        hasher.update(&[Fr::zero()]);
        let result = hasher.squeeze();
        println!("hash result is {:?}", result);
        assert_eq!(result.to_string(), ZERO_HASHER_SQUEEZE);
    }

    #[test]
    fn thread_local_merkle_hasher_resets_state() {
        let first = super::with_merkle_hasher(|hasher| {
            hasher
                .update_exact(&[Fr::from(1u64), Fr::from(2u64)])
                .to_repr()
        });
        let second = super::with_merkle_hasher(|hasher| {
            hasher
                .update_exact(&[Fr::from(3u64), Fr::from(4u64)])
                .to_repr()
        });

        let mut baseline = super::MERKLE_HASHER.clone();
        let expected_first = baseline
            .update_exact(&[Fr::from(1u64), Fr::from(2u64)])
            .to_repr();

        let mut baseline = super::MERKLE_HASHER.clone();
        let expected_second = baseline
            .update_exact(&[Fr::from(3u64), Fr::from(4u64)])
            .to_repr();

        assert_eq!(first, expected_first);
        assert_eq!(second, expected_second);
    }

    #[test]
    fn thread_local_leaf_hasher_resets_state() {
        let values = [Fr::from(5u64), Fr::from(6u64)];
        let threaded_hash = super::with_merkle_leaf_hasher(|hasher| {
            if cfg!(feature = "complex-leaf") {
                hasher.update(&values);
                hasher.squeeze().to_repr()
            } else {
                hasher.update_exact(&values).to_repr()
            }
        });

        let mut baseline = super::MERKLE_LEAF_HASHER.clone();
        let expected = if cfg!(feature = "complex-leaf") {
            baseline.update(&values);
            baseline.squeeze().to_repr()
        } else {
            baseline.update_exact(&values).to_repr()
        };

        assert_eq!(threaded_hash, expected);
    }

    #[test]
    fn thread_local_merkle_hasher_isolated_across_threads() {
        let expected_a = {
            let mut h = super::MERKLE_HASHER.clone();
            h.update_exact(&[Fr::from(7u64), Fr::from(8u64)]).to_repr()
        };
        let expected_b = {
            let mut h = super::MERKLE_HASHER.clone();
            h.update_exact(&[Fr::from(9u64), Fr::from(10u64)]).to_repr()
        };

        let handle_a = thread::spawn(|| {
            super::with_merkle_hasher(|h| {
                h.update_exact(&[Fr::from(7u64), Fr::from(8u64)]).to_repr()
            })
        });
        let handle_b = thread::spawn(|| {
            super::with_merkle_hasher(|h| {
                h.update_exact(&[Fr::from(9u64), Fr::from(10u64)]).to_repr()
            })
        });

        assert_eq!(handle_a.join().unwrap(), expected_a);
        assert_eq!(handle_b.join().unwrap(), expected_b);
    }

    #[test]
    fn thread_local_leaf_hasher_isolated_across_threads() {
        let values_a = [Fr::from(11u64), Fr::from(12u64)];
        let values_b = [Fr::from(13u64), Fr::from(14u64)];

        let expected_a = {
            let mut baseline = super::MERKLE_LEAF_HASHER.clone();
            if cfg!(feature = "complex-leaf") {
                baseline.update(&values_a);
                baseline.squeeze().to_repr()
            } else {
                baseline.update_exact(&values_a).to_repr()
            }
        };
        let expected_b = {
            let mut baseline = super::MERKLE_LEAF_HASHER.clone();
            if cfg!(feature = "complex-leaf") {
                baseline.update(&values_b);
                baseline.squeeze().to_repr()
            } else {
                baseline.update_exact(&values_b).to_repr()
            }
        };

        let handle_a = thread::spawn(move || {
            super::with_merkle_leaf_hasher(|h| {
                if cfg!(feature = "complex-leaf") {
                    h.update(&values_a);
                    h.squeeze().to_repr()
                } else {
                    h.update_exact(&values_a).to_repr()
                }
            })
        });

        let handle_b = thread::spawn(move || {
            super::with_merkle_leaf_hasher(|h| {
                if cfg!(feature = "complex-leaf") {
                    h.update(&values_b);
                    h.squeeze().to_repr()
                } else {
                    h.update_exact(&values_b).to_repr()
                }
            })
        });

        assert_eq!(handle_a.join().unwrap(), expected_a);
        assert_eq!(handle_b.join().unwrap(), expected_b);
    }
}
