use clap::Parser;
use std::cell::RefCell;
use std::path::PathBuf;
use std::rc::Rc;
use std::time::Instant;
use tempfile::tempdir;
use zkwasm_host_circuits::host::db::{RocksDB, TreeDB};
use zkwasm_host_circuits::host::merkle::MerkleTree;
use zkwasm_host_circuits::host::mongomerkle::{MongoMerkle, DEFAULT_HASH_VEC};
use zkwasm_host_circuits::constants::MERKLE_DEPTH;

#[derive(Parser, Debug)]
#[clap(version, about = "RocksDB-backed merkle update microbench")]
struct Args {
    /// Number of leaf updates.
    #[clap(long, default_value_t = 10_000)]
    iters: usize,

    /// Optional explicit RocksDB path (defaults to a temp dir).
    #[clap(long)]
    db_path: Option<PathBuf>,

    /// Leaf index offset (0 = sequential).
    #[clap(long, default_value_t = 0)]
    stride: u64,
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    let temp_dir;
    let db_path = match args.db_path {
        Some(path) => path,
        None => {
            temp_dir = tempdir()?;
            temp_dir.path().to_path_buf()
        }
    };

    let db: Rc<RefCell<dyn TreeDB>> = Rc::new(RefCell::new(RocksDB::new(&db_path)?));
    let root = DEFAULT_HASH_VEC[MERKLE_DEPTH];
    let mut mt = MongoMerkle::<MERKLE_DEPTH>::construct([0; 32], root, Some(db));

    let first_leaf = (1u64 << MERKLE_DEPTH) - 1;
    let mut data = vec![0u8; 32];

    let start = Instant::now();
    for i in 0..args.iters {
        let leaf_index = if args.stride == 0 {
            first_leaf + i as u64
        } else {
            first_leaf + (i as u64) * args.stride
        };
        data[..8].copy_from_slice(&(i as u64).to_le_bytes());
        mt.update_leaf_data_with_proof(leaf_index, &data)?;
    }
    let elapsed = start.elapsed();
    let seconds = elapsed.as_secs_f64().max(f64::MIN_POSITIVE);
    let tps = (args.iters as f64) / seconds;

    println!(
        "iters={} elapsed={:.3}s tps={:.2} root={:?}",
        args.iters,
        seconds,
        tps,
        mt.get_root_hash()
    );

    Ok(())
}
