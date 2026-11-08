//! Named, exact Goldilocks baseline: Plonky3's public DFT API, width one.
use p3_dft::{Radix2DitParallel, TwoAdicSubgroupDft};
use p3_field::{PrimeCharacteristicRing, PrimeField64, TwoAdicField};
use p3_goldilocks::Goldilocks as F;
use std::{hint::black_box, time::Instant};

fn main() {
    println!("# Plonky3 p3-dft 0.8.0 Radix2DitParallel<Goldilocks>; natural-order forward DFT; width=1");
    println!("# CPU wall time; warm twiddles; clone outside timer; includes dft API natural-order output conversion; no allocation/input construction outside API timed");
    println!("# rayon_threads={}; RUSTFLAGS={}", rayon::current_num_threads(), option_env!("RUSTFLAGS").unwrap_or("record in run.sh"));
    println!("log2_n\tn\tsamples\tmin_us\tmedian_us\tp90_us\tchecksum");
    for log in [10usize, 16, 20] {
        let n = 1usize << log;
        let input: Vec<F> = (0..n).map(|i| F::new((i as u64).wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407))).collect();
        let dft = Radix2DitParallel::<F>::default();
        let output = dft.dft(input.clone());
        assert_eq!(dft.idft(output.clone()), input, "DFT/inverse roundtrip");
        // Independent O(n) direct sums for selected frequencies, not merely roundtrip.
        let root = F::two_adic_generator(log);
        for k in [0usize, 1, 7, n-1] {
            let step = root.exp_u64(k as u64);
            let mut power = F::ONE;
            let mut sum = F::ZERO;
            for x in &input { sum += *x * power; power *= step; }
            assert_eq!(output[k], sum, "direct DFT frequency {k}");
        }
        for _ in 0..3 { black_box(dft.dft(input.clone())); }
        let mut times = Vec::new();
        let mut checksum = 0u64;
        for _ in 0..31 {
            let data = input.clone();
            let start = Instant::now();
            let result = black_box(dft.dft(black_box(data)));
            times.push(start.elapsed().as_secs_f64() * 1e6);
            checksum ^= result[n/3].as_canonical_u64();
        }
        times.sort_by(f64::total_cmp);
        println!("{log}\t{n}\t{}\t{:.3}\t{:.3}\t{:.3}\t{checksum}", times.len(), times[0], times[15], times[27]);
    }
}
