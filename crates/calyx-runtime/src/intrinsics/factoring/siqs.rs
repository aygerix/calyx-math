//! The self-initialising quadratic sieve (SIQS) behind `MPQS` and
//! `Factorization`.
//!
//! n is multiplied by a small k chosen by the Knuth-Schroeppel function,
//! and relations (a x + b)^2 = a g(x) mod kn are collected from polynomials
//! g(x) = a x^2 + 2 b x + c whose values are smooth over the factor base. a
//! is a product of s factor base primes, and its 2^(s-1) values of b are
//! taken in Gray code order, so that the sieve roots move by one addition
//! each. The interval [-M, M) is sieved in blocks that fit the L1 cache.
//! Primes up to a few blocks are sieved block by block (those above a block
//! without branches, as they hit it at most once per root); the larger ones
//! are pushed into per-block buckets once per polynomial. Relations with
//! one large prime are paired as they arrive, and block Lanczos finds the
//! dependencies.

use std::collections::{HashMap, HashSet};

use calyx_flint::Integer;

use super::super::numtheory::primes_up_to;

/// The sieve block: 32 KB, the L1 data cache of most machines.
const BLOCK_BITS: usize = 15;
const BLOCK: usize = 1 << BLOCK_BITS;

/// Relations wanted beyond the size of the factor base.
const EXTRA: usize = 64;

/// Primes below this are not sieved, only divided out of candidates.
const SMALL_PRIME: u32 = 100;

/// The bits by which a candidate's sieve value may fall short of the size
/// of g(x) over a large prime: they make up for the primes not sieved, the
/// prime powers and the values smaller than the largest.
const SLACK: f64 = 20.0;

/// Tuning by the bit size of kn, interpolated between the rows: the factor
/// base primes, the large prime bound as a multiple of the largest of them,
/// and the blocks sieved on each side of 0. Timed on the VM (a Zen 3 core)
/// from 30 to 75 digits; the larger rows follow the growth of the others.
const PARAMS: [(u64, usize, u64, usize); 16] = [
    (80, 60, 20, 1),
    (100, 100, 20, 1),
    (116, 200, 20, 1),
    (133, 400, 30, 1),
    (150, 700, 30, 1),
    (166, 1000, 40, 1),
    (183, 2300, 50, 1),
    (200, 4000, 60, 1),
    (216, 7000, 60, 1),
    (233, 15000, 80, 2),
    (250, 28000, 100, 2),
    (266, 40000, 100, 3),
    (283, 52000, 110, 3),
    (300, 60000, 120, 4),
    (316, 64000, 130, 5),
    (333, 65000, 140, 6),
];

/// The factor base size, large prime multiplier and blocks on each side for
/// kn of the given size.
fn params(bits: u64) -> (usize, u64, usize) {
    let i = PARAMS.partition_point(|r| r.0 < bits);
    if i == 0 || i == PARAMS.len() {
        let r = PARAMS[i.min(PARAMS.len() - 1)];
        return (r.1, r.2, r.3);
    }
    let (lo, hi) = (PARAMS[i - 1], PARAMS[i]);
    let t = (bits - lo.0) as f64 / (hi.0 - lo.0) as f64;
    let mix = |a: f64, b: f64| a + t * (b - a);
    (mix(lo.1 as f64, hi.1 as f64).round() as usize, mix(lo.2 as f64, hi.2 as f64).round() as u64, if t < 0.5 { lo.3 } else { hi.3 })
}

/// The largest kn the sieve takes on.
pub const MAX_BITS: u64 = 400;

// ----- arithmetic modulo word primes ---------------------------------------------------------

/// b^e mod p for p < 2^32.
fn powm(mut b: u64, mut e: u64, p: u64) -> u64 {
    let mut r = 1 % p;
    b %= p;
    while e > 0 {
        if e & 1 == 1 {
            r = r * b % p;
        }
        b = b * b % p;
        e >>= 1;
    }
    r
}

/// The inverse of a modulo p, for a coprime to p.
fn invm(a: u64, p: u64) -> u64 {
    let (mut r0, mut r1) = (p as i64, (a % p) as i64);
    let (mut t0, mut t1) = (0i64, 1i64);
    while r1 != 0 {
        let q = r0 / r1;
        (r0, r1) = (r1, r0 - q * r1);
        (t0, t1) = (t1, t0 - q * t1);
    }
    t0.rem_euclid(p as i64) as u64
}

/// The Jacobi symbol (a/n) for odd n.
fn jacobi(mut a: u64, mut n: u64) -> i32 {
    let mut t = 1;
    a %= n;
    while a != 0 {
        while a % 2 == 0 {
            a /= 2;
            if n % 8 == 3 || n % 8 == 5 {
                t = -t;
            }
        }
        (a, n) = (n, a);
        if a % 4 == 3 && n % 4 == 3 {
            t = -t;
        }
        a %= n;
    }
    if n == 1 { t } else { 0 }
}

/// A square root of the quadratic residue a modulo the odd prime p
/// (Tonelli-Shanks).
fn sqrtm(a: u64, p: u64) -> u64 {
    if p % 4 == 3 {
        return powm(a, (p + 1) / 4, p);
    }
    let (mut q, mut s) = (p - 1, 0);
    while q % 2 == 0 {
        q /= 2;
        s += 1;
    }
    let mut z = 2;
    while jacobi(z, p) != -1 {
        z += 1;
    }
    let (mut m, mut c, mut t, mut r) = (s, powm(z, q, p), powm(a, q, p), powm(a, q.div_ceil(2), p));
    while t != 1 {
        let (mut i, mut tt) = (0, t);
        while tt != 1 {
            tt = tt * tt % p;
            i += 1;
        }
        let b = powm(c, 1 << (m - i - 1), p);
        (m, c) = (i, b * b % p);
        (t, r) = (t * c % p, r * b % p);
    }
    r
}

/// The Knuth-Schroeppel multiplier: the odd squarefree k < 72 for which kn
/// is divisible by the most small primes on average.
fn multiplier(n: &Integer) -> u64 {
    const KS: [u64; 30] = [1, 3, 5, 7, 11, 13, 15, 17, 19, 21, 23, 29, 31, 33, 35, 37, 39, 41, 43, 47, 51, 53, 55, 57, 59, 61, 65, 67, 69, 71];
    let primes = primes_up_to(2000);
    let residues: Vec<u64> = primes[1..].iter().map(|&p| n.mod_u64(p)).collect();
    let n8 = n.mod_u64(8);
    let mut best = (f64::MIN, 1);
    for k in KS {
        let mut score = -0.5 * (k as f64).ln();
        score += match k * n8 % 8 {
            1 => 2.0,
            5 => 1.0,
            _ => 0.5,
        } * std::f64::consts::LN_2;
        for (&p, &r) in primes[1..].iter().zip(&residues) {
            let lp = (p as f64).ln();
            if k % p == 0 {
                score += lp / p as f64;
            } else if jacobi(k * r % p, p) == 1 {
                score += 2.0 * lp / (p - 1) as f64;
            }
        }
        if score > best.0 {
            best = (score, k);
        }
    }
    best.1
}

// ----- the values of the polynomials -----------------------------------------------------

/// A signed integer of up to 256 bits.
#[derive(Clone, Copy)]
struct Wide {
    neg: bool,
    mag: [u64; 4],
}

fn add_mag(a: &[u64; 4], b: &[u64; 4]) -> [u64; 4] {
    let mut out = [0; 4];
    let mut carry = false;
    for i in 0..4 {
        let (s, c1) = a[i].overflowing_add(b[i]);
        let (s, c2) = s.overflowing_add(carry as u64);
        out[i] = s;
        carry = c1 || c2;
    }
    out
}

/// a - b for a >= b.
fn sub_mag(a: &[u64; 4], b: &[u64; 4]) -> [u64; 4] {
    let mut out = [0; 4];
    let mut borrow = false;
    for i in 0..4 {
        let (d, b1) = a[i].overflowing_sub(b[i]);
        let (d, b2) = d.overflowing_sub(borrow as u64);
        out[i] = d;
        borrow = b1 || b2;
    }
    out
}

fn ge_mag(a: &[u64; 4], b: &[u64; 4]) -> bool {
    for i in (0..4).rev() {
        if a[i] != b[i] {
            return a[i] > b[i];
        }
    }
    true
}

impl Wide {
    fn from_integer(z: &Integer) -> Wide {
        let l = z.to_limbs();
        assert!(l.len() <= 4, "polynomial coefficient too large");
        let mut mag = [0; 4];
        mag[..l.len()].copy_from_slice(&l);
        Wide { neg: z.sign() < 0, mag }
    }

    fn is_zero(&self) -> bool {
        self.mag == [0; 4]
    }

    fn mul_small(&self, x: i64) -> Wide {
        let m = x.unsigned_abs() as u128;
        let mut mag = [0; 4];
        let mut carry = 0u128;
        for i in 0..4 {
            let t = self.mag[i] as u128 * m + carry;
            mag[i] = t as u64;
            carry = t >> 64;
        }
        Wide { neg: self.neg != (x < 0), mag }
    }

    fn add(&self, o: &Wide) -> Wide {
        if self.neg == o.neg {
            Wide { neg: self.neg, mag: add_mag(&self.mag, &o.mag) }
        } else if ge_mag(&self.mag, &o.mag) {
            Wide { neg: self.neg, mag: sub_mag(&self.mag, &o.mag) }
        } else {
            Wide { neg: o.neg, mag: sub_mag(&o.mag, &self.mag) }
        }
    }

    fn trailing_zeros(&self) -> u32 {
        for i in 0..4 {
            if self.mag[i] != 0 {
                return 64 * i as u32 + self.mag[i].trailing_zeros();
            }
        }
        256
    }

    fn shr(&mut self, k: u32) {
        let (w, b) = ((k / 64) as usize, k % 64);
        for i in 0..4 {
            let lo = self.mag.get(i + w).copied().unwrap_or(0);
            let hi = self.mag.get(i + w + 1).copied().unwrap_or(0);
            self.mag[i] = if b == 0 { lo } else { (lo >> b) | (hi << (64 - b)) };
        }
    }

    /// Divide by p if it divides; whether it did.
    fn div_exact(&mut self, p: u32) -> bool {
        let p = p as u64;
        let top = (0..4).rev().find(|&i| self.mag[i] != 0).unwrap_or(0);
        let mut q = [0u64; 4];
        let mut rem = 0u64;
        for i in (0..=top).rev() {
            let hi = (rem << 32) | (self.mag[i] >> 32);
            let lo = ((hi % p) << 32) | (self.mag[i] & 0xffff_ffff);
            q[i] = ((hi / p) << 32) | (lo / p);
            rem = lo % p;
        }
        if rem != 0 {
            return false;
        }
        self.mag = q;
        true
    }

    fn to_u64(&self) -> Option<u64> {
        (self.mag[1] | self.mag[2] | self.mag[3] == 0).then_some(self.mag[0])
    }
}

// ----- the factor base -----------------------------------------------------------------------

struct FactorBase {
    /// The primes, with 1 standing for -1 at index 0 and 2 at index 1.
    p: Vec<u32>,
    /// A square root of kn modulo p (0 where p divides kn).
    sqrt: Vec<u32>,
    /// ceil(2^40 / p): x mod p is x - p ((x ceil(2^40 / p)) >> 40) for
    /// x < 2^21 and p < 2^19.
    magic: Vec<u64>,
    /// The first prime sieved, and the first one above a block.
    med: usize,
    large: usize,
}

/// The first `size` primes p (with -1 and 2) for which kn is a square modulo
/// p, or a prime factor of n met on the way.
fn factor_base(n: &Integer, kn: &Integer, size: usize) -> Result<FactorBase, Integer> {
    let mut bound = (size as f64 * (size as f64 + 2.0).ln() * 2.5) as u64 + 1000;
    // Twice the bound finds twice the primes: a few rounds always suffice.
    for _ in 0..8 {
        let mut fb = FactorBase { p: vec![1, 2], sqrt: vec![0, 1], magic: vec![0, 0], med: 0, large: 0 };
        for &p in &primes_up_to(bound)[1..] {
            if fb.p.len() == size {
                break;
            }
            let r = kn.mod_u64(p);
            let t = if r == 0 {
                if n.mod_u64(p) == 0 {
                    return Err(Integer::from_u64(p));
                }
                0
            } else if jacobi(r, p) == 1 {
                sqrtm(r, p)
            } else {
                continue;
            };
            fb.p.push(p as u32);
            fb.sqrt.push(t as u32);
            fb.magic.push(((1u64 << 40) + p - 1) / p);
        }
        if fb.p.len() == size {
            fb.med = fb.p.iter().position(|&p| p >= SMALL_PRIME).unwrap_or(size);
            fb.large = fb.p.iter().position(|&p| p as usize >= BLOCK).unwrap_or(size);
            return Ok(fb);
        }
        bound *= 2;
    }
    unreachable!("the factor base bound doubles until it holds enough primes")
}

// ----- the sieve -----------------------------------------------------------------------------

/// A relation: y^2 is the product of `factors` (factor base indices, with
/// repetitions) and lp^2, modulo n.
struct Relation {
    y: Integer,
    factors: Vec<u32>,
    lp: u64,
}

struct Siqs<'a> {
    n: &'a Integer,
    kn: Integer,
    fb: FactorBase,
    /// The sieve interval is [-m, m), in `blocks` blocks.
    m: usize,
    blocks: usize,
    lp_bound: u64,
    /// The logarithms added by the sieve, and its starting value: a byte
    /// with its top bit set marks a candidate.
    logp: Vec<u8>,
    logp0: Vec<u8>,
    init: u8,
    target_bits: f64,
    rng: u64,
    used: HashSet<Vec<usize>>,

    // the current a: its primes, the B_j and 2 B_j / a modulo each prime
    a: Integer,
    qs: Vec<usize>,
    bs: Vec<Integer>,
    bainv: Vec<Vec<u32>>,
    // the current b, c and the roots of g modulo each prime, as positions
    // in the interval
    b: Integer,
    c: Integer,
    root1: Vec<u32>,
    root2: Vec<u32>,
    wa: Wide,
    wb2: Wide,
    wc: Wide,

    sieve: Vec<u8>,
    /// The primes from `large` to `split` are sieved block by block, and
    /// their hits in the block logged in log[..nlog]; the larger ones go
    /// through buckets.
    split: usize,
    log: Vec<u32>,
    nlog: usize,
    /// The bucket of block k is buckets[k * cap..][..fill[k]]: each prime
    /// above a block hits a block at most once per root.
    buckets: Vec<u32>,
    /// The logarithms of the large primes, by index from `large`.
    blog: Box<[u8; 1 << 16]>,
    fill: Vec<usize>,
    cap: usize,
    /// The logged and bucket entries of the current block at candidates.
    hits: Vec<u32>,
    next1: Vec<u32>,
    next2: Vec<u32>,

    rels: Vec<Relation>,
    partials: HashMap<u64, Relation>,
    seen: HashSet<u64>,
}

fn rand(state: &mut u64) -> u64 {
    let mut x = *state;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    *state = x;
    x.wrapping_mul(0x2545_f491_4f6c_dd1d)
}

// The stages are kept out of line: inlined into one loop they ran slower.
impl<'a> Siqs<'a> {
    fn new(n: &'a Integer, kn: Integer, fb: FactorBase, lp_mult: u64, blocks_per_side: usize) -> Siqs<'a> {
        let size = fb.p.len();
        let m = blocks_per_side * BLOCK;
        let pmax = *fb.p.last().unwrap() as u64;
        let lp_bound = (lp_mult * pmax).min(pmax * pmax);
        // Candidates must be smooth up to one large prime, in bits of the
        // largest values, less some for the small primes left out.
        let kn_bits = kn.to_f64().log2();
        let g_bits = kn_bits / 2.0 + (m as f64).log2() - 0.5;
        let thresh = g_bits - (lp_bound as f64).log2() - SLACK;
        let scale = if thresh > 100.0 { 100.0 / thresh } else { 1.0 };
        let logp: Vec<u8> = fb.p.iter().map(|&p| ((p as f64).log2() * scale).round() as u8).collect();
        let init = 128 - (thresh * scale).round() as u8;
        let target_bits = (kn_bits + 1.0) / 2.0 - (m as f64).log2();
        // Sieving a prime block by block costs a step per block and root,
        // and through buckets some more per hit: the second wins from about
        // 1 + 6 / blocks_per_side blocks.
        let split_at = (BLOCK + 6 * BLOCK / blocks_per_side) as u32;
        let split = fb.p.partition_point(|&p| p < split_at).max(fb.large);
        let mut blog = Box::new([0u8; 1 << 16]);
        for (b, &l) in blog.iter_mut().zip(&logp[fb.large..]) {
            *b = l;
        }
        Siqs {
            n,
            rng: n.hash_u64() | 1,
            kn,
            m,
            blocks: 2 * blocks_per_side,
            lp_bound,
            logp0: logp.clone(),
            logp,
            init,
            target_bits,
            used: HashSet::new(),
            a: Integer::zero(),
            qs: Vec::new(),
            bs: Vec::new(),
            bainv: Vec::new(),
            b: Integer::zero(),
            c: Integer::zero(),
            root1: vec![0; size],
            root2: vec![0; size],
            wa: Wide { neg: false, mag: [0; 4] },
            wb2: Wide { neg: false, mag: [0; 4] },
            wc: Wide { neg: false, mag: [0; 4] },
            sieve: vec![0; BLOCK],
            split,
            log: vec![0; 2 * (split - fb.large) + 1],
            nlog: 0,
            cap: 2 * (size - split),
            buckets: vec![0; 2 * blocks_per_side * 2 * (size - split)],
            blog,
            fill: vec![0; 2 * blocks_per_side],
            hits: Vec::new(),
            next1: vec![0; size],
            next2: vec![0; size],
            rels: Vec::new(),
            partials: HashMap::new(),
            seen: HashSet::new(),
            fb,
        }
    }

    /// The factor base indices of the primes of a new a near the target
    /// sqrt(2 kn) / M, or None when no new one turns up.
    #[inline(never)]
    fn choose_a(&mut self) -> Option<Vec<usize>> {
        let fb = &self.fb;
        // The primes of a come from below a block, above the unsieved ones,
        // and sit near 2000 when there is room.
        let lo = fb.med.max(2);
        let hi = fb.large.max(lo + 1);
        let (lo_bits, hi_bits) = ((fb.p[lo] as f64).log2(), (fb.p[hi - 1] as f64).log2());
        let mut s = 1;
        let mut best = f64::MAX;
        for k in 1..=20 {
            let q = self.target_bits / k as f64;
            let d = if q > hi_bits { 100.0 + q - hi_bits } else if q < lo_bits { 100.0 + lo_bits - q } else { (q - 11.0).abs() };
            if d < best {
                (best, s) = (d, k);
            }
        }
        let q_bits = self.target_bits / s as f64;
        // A window of primes around the ideal size.
        let centre = fb.p[lo..hi].partition_point(|&p| (p as f64).log2() < q_bits) + lo;
        let half = (4 * s + 8).max((hi - lo) / 8);
        let (wlo, whi) = (centre.saturating_sub(half).max(lo), (centre + half).min(hi));
        if whi - wlo < s {
            return None;
        }
        for _ in 0..1000 {
            let mut qs: Vec<usize> = Vec::with_capacity(s);
            let mut bits = 0.0;
            while qs.len() + 1 < s {
                let i = wlo + (rand(&mut self.rng) % (whi - wlo) as u64) as usize;
                if !qs.contains(&i) && fb.sqrt[i] != 0 {
                    qs.push(i);
                    bits += (fb.p[i] as f64).log2();
                }
            }
            // The last prime brings the product closest to the target.
            let want = self.target_bits - bits;
            let j = fb.p[lo..hi].partition_point(|&p| (p as f64).log2() < want) + lo;
            let j = [j.saturating_sub(1).max(lo), j.min(hi - 1)]
                .into_iter()
                .filter(|i| !qs.contains(i) && fb.sqrt[*i] != 0)
                .min_by(|&x, &y| ((fb.p[x] as f64).log2() - want).abs().total_cmp(&((fb.p[y] as f64).log2() - want).abs()));
            let Some(j) = j else { continue };
            if ((fb.p[j] as f64).log2() - want).abs() > 1.0 {
                continue;
            }
            qs.push(j);
            qs.sort_unstable();
            if self.used.insert(qs.clone()) {
                return Some(qs);
            }
        }
        None
    }

    /// Set up a = prod q_j with its B_j, the first b and the roots.
    #[inline(never)]
    fn new_a(&mut self, qs: Vec<usize>) {
        let fb = &self.fb;
        let s = qs.len();
        let q: Vec<u64> = qs.iter().map(|&i| fb.p[i] as u64).collect();
        let mut a = Integer::one();
        for &x in &q {
            a = &a * &Integer::from_u64(x);
        }
        // B_j = (a/q_j) gamma_j with gamma_j = sqrt(kn) (a/q_j)^-1 mod q_j,
        // at most q_j / 2, so that b = sum B_j has b^2 = kn mod a.
        let mut gammas = Vec::with_capacity(s);
        let mut bs = Vec::with_capacity(s);
        for j in 0..s {
            let aq = a.divexact(&Integer::from_u64(q[j]));
            let g = fb.sqrt[qs[j]] as u64 * invm(aq.mod_u64(q[j]), q[j]) % q[j];
            let g = g.min(q[j] - g);
            gammas.push(g);
            bs.push(&aq * &Integer::from_u64(g));
        }
        let mut b = Integer::zero();
        for bj in &bs {
            b = &b + bj;
        }
        let size = fb.p.len();
        let mut bainv = vec![vec![0u32; size]; s];
        let mut prefix = vec![0u64; s + 1];
        let mut suffix = vec![0u64; s + 1];
        for i in 2..size {
            let p = fb.p[i] as u64;
            if qs.contains(&i) {
                continue;
            }
            // a/q_j mod p from prefix and suffix products of the q's.
            prefix[0] = 1;
            for j in 0..s {
                prefix[j + 1] = prefix[j] * (q[j] % p) % p;
            }
            suffix[s] = 1;
            for j in (0..s).rev() {
                suffix[j] = suffix[j + 1] * (q[j] % p) % p;
            }
            let ainv = invm(prefix[s], p);
            let mut bm = 0;
            for j in 0..s {
                let bj = prefix[j] * suffix[j + 1] % p * (gammas[j] % p) % p;
                bm = (bm + bj) % p;
                bainv[j][i] = (2 * bj % p * ainv % p) as u32;
            }
            let (t, mm) = (fb.sqrt[i] as u64, (self.m as u64) % p);
            self.root1[i] = ((ainv * ((t + p - bm) % p) % p + mm) % p) as u32;
            self.root2[i] = ((ainv * ((2 * p - t - bm) % p) % p + mm) % p) as u32;
        }
        // The primes of a divide g at one root, set with each b; they are
        // not sieved.
        for &i in &self.qs {
            self.logp[i] = self.logp0[i];
        }
        for &i in &qs {
            self.logp[i] = 0;
        }
        self.a = a;
        self.qs = qs;
        self.bs = bs;
        self.bainv = bainv;
        self.b = b;
        self.set_poly();
    }

    /// c = (b^2 - kn)/a, the roots at the primes of a, and the wide copies.
    #[inline(never)]
    fn set_poly(&mut self) {
        self.c = (&(&self.b * &self.b) - &self.kn).divexact(&self.a);
        for &i in &self.qs {
            let p = self.fb.p[i] as u64;
            // g = 2 b x + c mod p: x = -c / 2b.
            let r = (p - self.c.mod_u64(p)) % p * invm(2 * self.b.mod_u64(p) % p, p) % p;
            self.root1[i] = ((r + self.m as u64 % p) % p) as u32;
            self.root2[i] = self.root1[i];
        }
        self.wa = Wide::from_integer(&self.a);
        self.wb2 = Wide::from_integer(&(&self.b * 2));
        self.wc = Wide::from_integer(&self.c);
    }

    /// Move to the i-th b of the Gray code (i > 0): one B_v changes sign.
    #[inline(never)]
    fn next_b(&mut self, i: usize) {
        let v = i.trailing_zeros() as usize;
        let neg = ((i ^ (i >> 1)) >> v) & 1 == 1;
        let two_bv = &self.bs[v] * 2;
        let (p, d) = (&self.fb.p[..], &self.bainv[v][..]);
        // The roots a^-1 (±t - b) move against b.
        if neg {
            self.b = &self.b - &two_bv;
            for (((r1, r2), &d), &p) in self.root1.iter_mut().zip(self.root2.iter_mut()).zip(d).zip(p) {
                let (x, y) = (*r1 + d, *r2 + d);
                *r1 = if x >= p { x - p } else { x };
                *r2 = if y >= p { y - p } else { y };
            }
        } else {
            self.b = &self.b + &two_bv;
            for (((r1, r2), &d), &p) in self.root1.iter_mut().zip(self.root2.iter_mut()).zip(d).zip(p) {
                let (x, y) = (r1.wrapping_sub(d), r2.wrapping_sub(d));
                *r1 = if *r1 < d { x.wrapping_add(p) } else { x };
                *r2 = if *r2 < d { y.wrapping_add(p) } else { y };
            }
        }
        self.set_poly();
    }

    /// Push the hits of the primes from `split` on into the block buckets.
    #[inline(never)]
    fn fill_buckets(&mut self) {
        let interval = 2 * self.m;
        let (large, cap) = (self.fb.large, self.cap);
        let mut fill = [0usize; 64];
        for k in 0..self.blocks {
            fill[k] = k * cap;
        }
        let buckets = &mut self.buckets[..];
        for i in self.split..self.fb.p.len() {
            let p = self.fb.p[i] as usize;
            let tag = ((i - large) as u32) << 16;
            for r in [self.root1[i], self.root2[i]] {
                let mut pos = r as usize;
                while pos < interval {
                    let k = pos >> BLOCK_BITS;
                    buckets[fill[k]] = tag | (pos & (BLOCK - 1)) as u32;
                    fill[k] += 1;
                    pos += p;
                }
            }
        }
        for k in 0..self.blocks {
            self.fill[k] = fill[k] - k * cap;
        }
    }

    /// Sieve one block with the primes below a block size, from and back
    /// into next1 and next2.
    #[inline(never)]
    fn sieve_medium(&mut self) {
        let sieve: &mut [u8; BLOCK] = (&mut self.sieve[..]).try_into().unwrap();
        sieve.fill(self.init);
        let r = self.fb.med..self.fb.large;
        let primes = self.fb.p[r.clone()].iter().zip(&self.logp[r.clone()]);
        for ((&p, &l), (n1, n2)) in primes.zip(self.next1[r.clone()].iter_mut().zip(&mut self.next2[r])) {
            let p = p as usize;
            // Both roots at once, the lower one leading.
            let (o1, o2) = (*n1 as usize, *n2 as usize);
            let (mut o, diff) = if o1 <= o2 { (o1, o2 - o1) } else { (o2, o1 - o2) };
            while o + diff < BLOCK {
                sieve[o] = sieve[o].wrapping_add(l);
                sieve[o + diff] = sieve[o + diff].wrapping_add(l);
                o += p;
            }
            let hi = o + diff;
            if o < BLOCK {
                sieve[o] = sieve[o].wrapping_add(l);
                o += p;
            }
            *n1 = (o - BLOCK) as u32;
            *n2 = (hi - BLOCK) as u32;
        }
    }

    /// Sieve one block with the primes from `large` to `split`, which hit it
    /// at most once at each root, and log the hits. Without branches: a miss
    /// adds 0 somewhere and is not counted.
    #[inline(never)]
    fn sieve_large(&mut self) {
        let sieve: &mut [u8; BLOCK] = (&mut self.sieve[..]).try_into().unwrap();
        let r = self.fb.large..self.split;
        let log = &mut self.log[..];
        let mut n = 0;
        let primes = self.fb.p[r.clone()].iter().zip(&self.logp[r.clone()]);
        for (k, ((&p, &l), (n1, n2))) in primes.zip(self.next1[r.clone()].iter_mut().zip(&mut self.next2[r])).enumerate() {
            let p = p as usize;
            let tag = (k as u32) << 16;
            for o in [n1, n2] {
                let x = *o as usize;
                let hit = x < BLOCK;
                let at = x & (BLOCK - 1);
                sieve[at] = sieve[at].wrapping_add(if hit { l } else { 0 });
                log[n] = tag | at as u32;
                n += hit as usize;
                *o = (x + if hit { p } else { 0 } - BLOCK) as u32;
            }
        }
        self.nlog = n;
    }

    /// Add the bucket of a block and list its candidates.
    #[inline(never)]
    fn apply_and_scan(&mut self, blk: usize, cands: &mut Vec<usize>) {
        let sieve: &mut [u8; BLOCK] = (&mut self.sieve[..]).try_into().unwrap();
        let bucket = &self.buckets[blk * self.cap..][..self.fill[blk]];
        for &e in bucket {
            let o = (e as usize) & (BLOCK - 1);
            sieve[o] = sieve[o].wrapping_add(self.blog[(e >> 16) as usize]);
        }
        cands.clear();
        for (w, chunk) in sieve.chunks_exact(64).enumerate() {
            let any = chunk.chunks_exact(8).fold(0, |a, q| a | u64::from_le_bytes(q.try_into().unwrap()));
            if any & 0x8080_8080_8080_8080 != 0 {
                for (k, &byte) in chunk.iter().enumerate() {
                    if byte & 0x80 != 0 {
                        cands.push(64 * w + k);
                    }
                }
            }
        }
        if cands.is_empty() {
            return;
        }
        self.hits.clear();
        for &e in self.log[..self.nlog].iter().chain(bucket) {
            if sieve[(e as usize) & (BLOCK - 1)] & 0x80 != 0 {
                self.hits.push(e);
            }
        }
    }

    /// Sieve the interval for the current polynomial and keep the relations.
    fn sieve_poly(&mut self) {
        self.fill_buckets();
        let (med, split) = (self.fb.med, self.split);
        self.next1[med..split].copy_from_slice(&self.root1[med..split]);
        self.next2[med..split].copy_from_slice(&self.root2[med..split]);
        let mut cands = Vec::new();
        for blk in 0..self.blocks {
            self.sieve_medium();
            self.sieve_large();
            self.apply_and_scan(blk, &mut cands);
            for &off in &cands {
                self.check(off + blk * BLOCK);
            }
        }
    }

    /// Trial divide g(x) at a candidate, and keep it if it is smooth up to
    /// one large prime.
    #[inline(never)]
    fn check(&mut self, pos: usize) {
        let off = pos & (BLOCK - 1);
        let x = pos as i64 - self.m as i64;
        let mut g = self.wa.mul_small(x).add(&self.wb2).mul_small(x).add(&self.wc);
        if g.is_zero() {
            return;
        }
        let fb = &self.fb;
        let mut fs: Vec<u32> = Vec::with_capacity(48);
        fs.extend(self.qs.iter().map(|&i| i as u32));
        if g.neg {
            fs.push(0);
        }
        let tz = g.trailing_zeros();
        g.shr(tz);
        fs.extend(std::iter::repeat_n(1, tz as usize));
        let pos64 = pos as u64;
        for i in 2..fb.large {
            let p = fb.p[i];
            let r = (pos64 - ((pos64 * fb.magic[i]) >> 40) * p as u64) as u32;
            if r == self.root1[i] || r == self.root2[i] {
                while g.div_exact(p) {
                    fs.push(i as u32);
                }
            }
        }
        for &e in &self.hits {
            if (e as usize) & (BLOCK - 1) == off {
                let i = fb.large + (e >> 16) as usize;
                while g.div_exact(fb.p[i]) {
                    fs.push(i as u32);
                }
            }
        }
        let Some(rest) = g.to_u64() else { return };
        if rest >= self.lp_bound {
            return;
        }
        let y = &(&self.a * &Integer::from_i64(x)) + &self.b;
        if !self.seen.insert(y.hash_u64()) {
            return;
        }
        if rest == 1 {
            self.rels.push(Relation { y, factors: fs, lp: 1 });
        } else if let Some(other) = self.partials.get(&rest) {
            // Two relations with the same large prime make one with its
            // square.
            let mut factors = other.factors.clone();
            factors.extend_from_slice(&fs);
            let y = (&other.y * &y).div_rem_euclid(self.n).unwrap().1;
            self.rels.push(Relation { y, factors, lp: rest });
        } else {
            self.partials.insert(rest, Relation { y, factors: fs, lp: rest });
        }
    }

    /// A proper factor of n from the dependencies among the relations.
    #[inline(never)]
    fn combine(&mut self) -> Option<Integer> {
        let size = self.fb.p.len();
        let mut cols: Vec<Vec<u32>> = Vec::with_capacity(self.rels.len());
        for r in &self.rels {
            let mut f = r.factors.clone();
            f.sort_unstable();
            let mut odd = Vec::with_capacity(f.len());
            for x in f {
                if odd.last() == Some(&x) {
                    odd.pop();
                } else {
                    odd.push(x);
                }
            }
            cols.push(odd);
        }
        let mut col_rel: Vec<usize> = (0..self.rels.len()).collect();
        let nrows = reduce_matrix(size, &mut cols, &mut col_rel);
        if cols.len() <= nrows {
            return None;
        }
        let deps = block_lanczos(nrows, &cols, &mut self.rng)?;
        let mut exps = vec![0u32; size];
        for bit in 0..64 {
            let mask = 1u64 << bit;
            let set: Vec<usize> = (0..cols.len()).filter(|&c| deps[c] & mask != 0).map(|c| col_rel[c]).collect();
            if set.is_empty() {
                continue;
            }
            exps.fill(0);
            let (mut x, mut z) = (Integer::one(), Integer::one());
            for &r in &set {
                let rel = &self.rels[r];
                x = (&x * &rel.y).div_rem_euclid(self.n).unwrap().1;
                for &f in &rel.factors {
                    exps[f as usize] += 1;
                }
                if rel.lp > 1 {
                    z = (&z * &Integer::from_u64(rel.lp)).div_rem_euclid(self.n).unwrap().1;
                }
            }
            for i in 1..size {
                debug_assert!(exps[i] % 2 == 0, "dependency with an odd exponent");
                if exps[i] > 0 {
                    let pe = Integer::from_u64(self.fb.p[i] as u64).powm(&Integer::from_u64((exps[i] / 2) as u64), self.n).unwrap();
                    z = (&z * &pe).div_rem_euclid(self.n).unwrap().1;
                }
            }
            let d = (&x - &z).gcd(self.n);
            if !d.is_one() && &d != self.n {
                return Some(d);
            }
        }
        None
    }
}

/// A proper factor of the odd composite n, which must not be a perfect
/// power and must have at most `MAX_BITS` bits; None if the sieve fails.
pub fn siqs(n: &Integer) -> Option<Integer> {
    let k = multiplier(n);
    let kn = n * &Integer::from_u64(k);
    let bits = kn.bits();
    if bits > MAX_BITS {
        return None;
    }
    let (size, lp_mult, blocks) = params(bits);
    let fb = match factor_base(n, &kn, size) {
        Ok(fb) => fb,
        Err(p) => return Some(p),
    };
    let mut siqs = Siqs::new(n, kn, fb, lp_mult, blocks);
    let mut target = size + EXTRA;
    // A bound on the polynomials, far above what any factorization needs.
    let max_polys = 1000 * size + 1_000_000;
    let mut polys = 0;
    for _ in 0..4 {
        while siqs.rels.len() < target {
            let qs = siqs.choose_a()?;
            let count = 1usize << (qs.len() - 1);
            siqs.new_a(qs);
            for i in 0..count {
                if i > 0 {
                    siqs.next_b(i);
                }
                siqs.sieve_poly();
            }
            polys += count;
            if polys > max_polys {
                return None;
            }
        }
        if let Some(d) = siqs.combine() {
            return Some(d);
        }
        target = siqs.rels.len() + size / 10 + EXTRA;
    }
    None
}

// ----- linear algebra --------------------------------------------------------------------------

/// Drop the columns with an entry in a row that has no other, until there
/// are none, keeping at most EXTRA more columns than rows; then number the
/// rows left from 0. Returns the number of rows.
fn reduce_matrix(nrows: usize, cols: &mut Vec<Vec<u32>>, col_rel: &mut Vec<usize>) -> usize {
    let mut counts = vec![0u32; nrows];
    for c in cols.iter() {
        for &r in c {
            counts[r as usize] += 1;
        }
    }
    let mut rows = nrows;
    // Each round removes rows or stops.
    for _ in 0..nrows + 1 {
        loop {
            let before = cols.len();
            let mut j = 0;
            for i in 0..cols.len() {
                if cols[i].iter().any(|&r| counts[r as usize] < 2) {
                    for &r in &cols[i] {
                        counts[r as usize] -= 1;
                    }
                } else {
                    cols.swap(i, j);
                    col_rel.swap(i, j);
                    j += 1;
                }
            }
            cols.truncate(j);
            col_rel.truncate(j);
            if cols.len() == before {
                break;
            }
        }
        let live = counts.iter().filter(|&&c| c > 0).count();
        if cols.len() > live + EXTRA {
            for c in &cols[live + EXTRA..] {
                for &r in c {
                    counts[r as usize] -= 1;
                }
            }
            cols.truncate(live + EXTRA);
            col_rel.truncate(live + EXTRA);
        }
        if live == rows {
            break;
        }
        rows = live;
    }
    let mut map = vec![0u32; nrows];
    let mut j = 0;
    for i in 0..nrows {
        if counts[i] > 0 {
            map[i] = j;
            j += 1;
        }
    }
    for c in cols.iter_mut() {
        for r in c.iter_mut() {
            *r = map[*r as usize];
        }
    }
    j as usize
}

/// c = a b for 64 x 64 matrices over GF(2), as 64 rows of 64 bits.
fn mul_64x64(a: &[u64; 64], b: &[u64; 64]) -> [u64; 64] {
    let mut c = [0u64; 64];
    for i in 0..64 {
        let (mut ai, mut acc, mut j) = (a[i], 0u64, 0);
        while ai != 0 {
            if ai & 1 == 1 {
                acc ^= b[j];
            }
            ai >>= 1;
            j += 1;
        }
        c[i] = acc;
    }
    c
}

/// y ^= v x for an n x 64 matrix v and a 64 x 64 matrix x, by tables of
/// the products of x with each byte.
fn mul_nx64_acc(v: &[u64], x: &[u64; 64], y: &mut [u64]) {
    let mut t = vec![0u64; 8 * 256];
    for j in 0..8 {
        for i in 0..256 {
            let (mut idx, mut acc, mut k) = (i, 0u64, 0);
            while idx != 0 {
                if idx & 1 == 1 {
                    acc ^= x[8 * j + k];
                }
                idx >>= 1;
                k += 1;
            }
            t[256 * j + i] = acc;
        }
    }
    for (yi, &w) in y.iter_mut().zip(v) {
        let mut acc = 0;
        for j in 0..8 {
            acc ^= t[256 * j + ((w >> (8 * j)) & 0xff) as usize];
        }
        *yi ^= acc;
    }
}

/// x^T y for n x 64 matrices x and y.
fn mul_64xn(x: &[u64], y: &[u64]) -> [u64; 64] {
    let mut t = vec![0u64; 8 * 256];
    for (&xi, &yi) in x.iter().zip(y) {
        for j in 0..8 {
            t[256 * j + ((xi >> (8 * j)) & 0xff) as usize] ^= yi;
        }
    }
    let mut xy = [0u64; 64];
    for i in 0..8 {
        let mut acc = [0u64; 8];
        for j in 0..256 {
            if (j >> i) & 1 == 1 {
                for (k, a) in acc.iter_mut().enumerate() {
                    *a ^= t[256 * k + j];
                }
            }
        }
        for (k, a) in acc.iter().enumerate() {
            xy[8 * k + i] = *a;
        }
    }
    xy
}

/// Find an invertible submatrix of t using the columns not in `last_s`
/// first, returning its inverse (as a 64 x 64 matrix) and the columns in it;
/// None if the columns of t and last_s do not cover all 64.
fn find_nonsingular_sub(t: &[u64; 64], last_s: &[usize]) -> Option<([u64; 64], Vec<usize>)> {
    let mut m = [[0u64; 2]; 64];
    for i in 0..64 {
        m[i] = [t[i], 1u64 << i];
    }
    let mut cols = [0usize; 64];
    let mut mask = 0u64;
    for (i, &c) in last_s.iter().enumerate() {
        cols[63 - i] = c;
        mask |= 1 << c;
    }
    let mut j = 0;
    for i in 0..64 {
        if mask & (1 << i) == 0 {
            cols[j] = i;
            j += 1;
        }
    }
    let mut s = Vec::new();
    for i in 0..64 {
        let bit = 1u64 << cols[i];
        // A pivot row for column cols[i].
        if let Some(j) = (i..64).find(|&j| m[cols[j]][0] & bit != 0) {
            m.swap(cols[i], cols[j]);
            let pivot = m[cols[i]];
            for j in 0..64 {
                if j != i && m[cols[j]][0] & bit != 0 {
                    m[cols[j]][0] ^= pivot[0];
                    m[cols[j]][1] ^= pivot[1];
                }
            }
            s.push(cols[i]);
            continue;
        }
        // Otherwise use the inverse half to compensate.
        let j = (i..64).find(|&j| m[cols[j]][1] & bit != 0)?;
        m.swap(cols[i], cols[j]);
        let pivot = m[cols[i]];
        for j in 0..64 {
            if j != i && m[cols[j]][1] & bit != 0 {
                m[cols[j]][0] ^= pivot[0];
                m[cols[j]][1] ^= pivot[1];
            }
        }
        m[cols[i]] = [0, 0];
    }
    let mut w = [0u64; 64];
    for i in 0..64 {
        w[i] = m[i][1];
    }
    let mut cover = 0u64;
    for &c in s.iter().chain(last_s) {
        cover |= 1 << c;
    }
    (cover == u64::MAX).then_some((w, s))
}

/// b = B x for the matrix with columns `cols`.
fn mul_b(nrows: usize, cols: &[Vec<u32>], x: &[u64]) -> Vec<u64> {
    let mut b = vec![0u64; nrows.max(cols.len())];
    for (c, &xc) in cols.iter().zip(x) {
        for &r in c {
            b[r as usize] ^= xc;
        }
    }
    b
}

/// B^T y.
fn mul_bt(cols: &[Vec<u32>], y: &[u64], out: &mut [u64]) {
    for (c, o) in cols.iter().zip(out.iter_mut()) {
        *o = c.iter().fold(0, |acc, &r| acc ^ y[r as usize]);
    }
}

/// Turn the columns of x and v, which span nullspace vectors of B together
/// with ax = B x and av = B v, into up to 64 vectors x with B x = 0, by
/// Gaussian elimination on the columns of [ax | av] mirrored in [x | v].
fn combine_cols(n: usize, x: &mut [u64], v: &[u64], ax: &[u64], av: &[u64]) {
    let words = n.div_ceil(64);
    // Transposed: row k of `mat` is column k of [x | v].
    let mut mat = vec![vec![0u64; words]; 128];
    let mut amat = vec![vec![0u64; words]; 128];
    for i in 0..n {
        let (w, bit) = (i / 64, 1u64 << (i % 64));
        for k in 0..64 {
            if x[i] >> k & 1 == 1 {
                mat[k][w] |= bit;
            }
            if v[i] >> k & 1 == 1 {
                mat[64 + k][w] |= bit;
            }
            if ax[i] >> k & 1 == 1 {
                amat[k][w] |= bit;
            }
            if av[i] >> k & 1 == 1 {
                amat[64 + k][w] |= bit;
            }
        }
    }
    let mut i = 0;
    for bitpos in 0..n {
        if i == 128 {
            break;
        }
        let (w, bit) = (bitpos / 64, 1u64 << (bitpos % 64));
        let Some(j) = (i..128).find(|&j| amat[j][w] & bit != 0) else { continue };
        mat.swap(i, j);
        amat.swap(i, j);
        for j in i + 1..128 {
            if amat[j][w] & bit != 0 {
                for k in 0..words {
                    amat[j][k] ^= amat[i][k];
                    mat[j][k] ^= mat[i][k];
                }
            }
        }
        i += 1;
    }
    // Rows i.. of [ax | av] are zero: those of [x | v] are dependencies.
    for (j, xj) in x.iter_mut().enumerate().take(n) {
        let (w, bit) = (j / 64, 1u64 << (j % 64));
        let mut word = 0u64;
        for k in i..64 {
            if mat[k][w] & bit != 0 {
                word |= 1 << k;
            }
        }
        *xj = word;
    }
}

/// Block Lanczos over GF(2) (Montgomery), after the msieve version by Jason
/// Papadopoulos in FLINT: up to 64 vectors x with B x = 0 for the matrix
/// with columns `cols` over `nrows` rows, packed in the bits of the words
/// x[i]; None if the iteration breaks down.
fn block_lanczos(nrows: usize, cols: &[Vec<u32>], rng: &mut u64) -> Option<Vec<u64>> {
    let n = cols.len();
    let vsize = nrows.max(n);
    let mut v: [Vec<u64>; 3] = [vec![0; vsize], vec![0; vsize], vec![0; vsize]];
    let mut vnext = vec![0u64; vsize];
    let mut winv: [[u64; 64]; 3] = [[0; 64]; 3];
    let mut vt_a_v: [[u64; 64]; 2] = [[0; 64]; 2];
    let mut vt_a2_v: [[u64; 64]; 2] = [[0; 64]; 2];
    let mut s: [Vec<usize>; 2] = [Vec::new(), (0..64).collect()];
    let mut mask1 = u64::MAX;

    // x starts off random and v0 = A x, for A = B^T B.
    for w in v[0].iter_mut().take(n) {
        *w = rand(rng);
    }
    let mut x = v[0].clone();
    let bx = mul_b(nrows, cols, &v[0]);
    mul_bt(cols, &bx, &mut v[0]);
    let v0 = v[0].clone();

    let mut dim0 = 0;
    let mut done = false;
    // The iteration takes about n/63 steps.
    for _ in 0..n / 32 + 64 {
        let bv = mul_b(nrows, cols, &v[0]);
        mul_bt(cols, &bv, &mut vnext);
        vt_a_v[0] = mul_64xn(&v[0][..n], &vnext[..n]);
        vt_a2_v[0] = mul_64xn(&vnext[..n], &vnext[..n]);
        if vt_a_v[0].iter().all(|&w| w == 0) {
            done = true;
            break;
        }
        let (w0, s0) = find_nonsingular_sub(&vt_a_v[0], &s[1])?;
        dim0 = s0.len();
        if dim0 == 0 {
            return None;
        }
        winv[0] = w0;
        s[0] = s0;
        let mask0 = s[0].iter().fold(0u64, |m, &c| m | 1 << c);

        let mut d = [0u64; 64];
        for i in 0..64 {
            d[i] = (vt_a2_v[0][i] & mask0) ^ vt_a_v[0][i];
        }
        d = mul_64x64(&winv[0], &d);
        for (i, di) in d.iter_mut().enumerate() {
            *di ^= 1 << i;
        }
        let mut e = mul_64x64(&winv[1], &vt_a_v[0]);
        for ei in e.iter_mut() {
            *ei &= mask0;
        }
        let mut f = mul_64x64(&vt_a_v[1], &winv[1]);
        for (i, fi) in f.iter_mut().enumerate() {
            *fi ^= 1 << i;
        }
        f = mul_64x64(&winv[2], &f);
        let mut f2 = [0u64; 64];
        for i in 0..64 {
            f2[i] = ((vt_a2_v[1][i] & mask1) ^ vt_a_v[1][i]) & mask0;
        }
        f = mul_64x64(&f, &f2);

        for w in vnext[..n].iter_mut() {
            *w &= mask0;
        }
        mul_nx64_acc(&v[0][..n], &d, &mut vnext[..n]);
        mul_nx64_acc(&v[1][..n], &e, &mut vnext[..n]);
        mul_nx64_acc(&v[2][..n], &f, &mut vnext[..n]);

        let mut dx = mul_64xn(&v[0][..n], &v0[..n]);
        dx = mul_64x64(&winv[0], &dx);
        mul_nx64_acc(&v[0][..n], &dx, &mut x[..n]);

        let old = std::mem::replace(&mut v[2], Vec::new());
        v[2] = std::mem::replace(&mut v[1], Vec::new());
        v[1] = std::mem::replace(&mut v[0], Vec::new());
        v[0] = std::mem::replace(&mut vnext, old);
        winv[2] = winv[1];
        winv[1] = winv[0];
        vt_a_v[1] = vt_a_v[0];
        vt_a2_v[1] = vt_a2_v[0];
        s[1] = s[0].clone();
        mask1 = mask0;
    }
    if !done || dim0 == 0 {
        return None;
    }
    let ax = mul_b(nrows, cols, &x);
    let av = mul_b(nrows, cols, &v[0]);
    combine_cols(n, &mut x, &v[0], &ax, &av);
    let bx = mul_b(nrows, cols, &x);
    if bx.iter().any(|&w| w != 0) {
        return None;
    }
    x.truncate(n);
    Some(x)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn z(s: &str) -> Integer {
        Integer::parse(s).unwrap()
    }

    #[test]
    fn modular_helpers() {
        for p in [3u64, 5, 7, 13, 17, 41, 97, 65537, 1_000_003] {
            for a in 1..40 {
                if jacobi(a, p) == 1 {
                    let r = sqrtm(a % p, p);
                    assert_eq!(r * r % p, a % p, "sqrt {a} mod {p}");
                }
                if a % p != 0 {
                    assert_eq!(a * invm(a, p) % p, 1);
                }
            }
        }
    }

    #[test]
    fn lanczos_finds_dependencies() {
        // A random sparse matrix with more columns than rows.
        let mut rng = 12345u64;
        let (nrows, ncols) = (300, 400);
        let cols: Vec<Vec<u32>> = (0..ncols)
            .map(|_| {
                let mut c: Vec<u32> = (0..10).map(|_| (rand(&mut rng) % nrows as u64) as u32).collect();
                c.sort_unstable();
                c.dedup();
                c
            })
            .collect();
        let x = block_lanczos(nrows, &cols, &mut rng).expect("lanczos");
        assert!(x.iter().any(|&w| w != 0));
        let b = mul_b(nrows, &cols, &x);
        assert!(b.iter().all(|&w| w == 0));
    }

    #[test]
    fn splits_semiprimes() {
        for s in ["1000000016000000063", "108215130879615765402700048513", "10821513087944168469130630000069003", "108215130879440000013925925399000000000063801"] {
            let n = z(s);
            let d = siqs(&n).unwrap_or_else(|| panic!("no factor of {n}"));
            assert!(!d.is_one() && d != n && n.is_divisible_by(&d), "{d} for {n}");
        }
    }
}
