use crate::host::datahash::DataHashRecord;
use crate::host::mongomerkle::MerkleRecord;
use lru::LruCache;
use parking_lot::Mutex;
use std::num::NonZeroUsize;

// If maxsize is set to None, the LRU feature is disabled and the cache can grow without bound.
// The LRU feature performs best when maxsize is a power-of-two.
const DEFAULT_CACHE_SIZE: usize = usize::pow(2, 24);

const ENV_CACHE_SIZE: &str = "ZKWASM_MERKLE_CACHE_SIZE";
const ENV_CACHE_SHARDS: &str = "ZKWASM_MERKLE_CACHE_SHARDS";
const DEFAULT_CACHE_SHARDS: usize = 16;

lazy_static::lazy_static! {
    pub static ref MERKLE_CACHE: Vec<Mutex<LruCache<[u8;  32], Option<MerkleRecord>>>> = {
        let shards = get_cache_shards();
        let total = get_cache_size();
        let per_shard = (total + shards - 1) / shards;
        let cap = NonZeroUsize::new(std::cmp::max(1, per_shard)).unwrap();
        (0..shards)
            .map(|_| Mutex::new(LruCache::<[u8; 32], Option<MerkleRecord>>::new(cap)))
            .collect()
    };

    pub static ref DATA_CACHE: Vec<Mutex<LruCache<[u8; 32], Option<DataHashRecord>>>> = {
        let shards = get_cache_shards();
        let total = get_cache_size();
        let per_shard = (total + shards - 1) / shards;
        let cap = NonZeroUsize::new(std::cmp::max(1, per_shard)).unwrap();
        (0..shards)
            .map(|_| Mutex::new(LruCache::<[u8; 32], Option<DataHashRecord>>::new(cap)))
            .collect()
    };
}

fn get_cache_size() -> usize {
    if let Ok(size_var) = std::env::var(ENV_CACHE_SIZE) {
        return size_var.parse::<usize>().unwrap_or(DEFAULT_CACHE_SIZE);
    }
    DEFAULT_CACHE_SIZE
}

fn get_cache_shards() -> usize {
    if let Ok(size_var) = std::env::var(ENV_CACHE_SHARDS) {
        if let Ok(v) = size_var.parse::<usize>() {
            return std::cmp::max(1, v);
        }
    }
    DEFAULT_CACHE_SHARDS
}
