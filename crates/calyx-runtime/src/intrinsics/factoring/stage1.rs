//! Stage 1 of ECM and the p ± 1 methods: the element raised (in the
//! method's sense) to every prime up to B1, each to the largest power at
//! most B1, packed into words and those into chunks.

use calyx_flint::Integer;

use crate::intrinsics::numtheory::each_prime;

/// The words in a chunk, between two gcds.
pub const CHUNK: usize = 64;

/// Run stage 1 from x. `step(x, ws)` applies the product of the words `ws`
/// to x, and `test(x)` is the gcd with n that reveals a factor. The gcd is
/// taken after each chunk; when it is n, the chunk is applied again a
/// prime at a time from where it began, to separate the factors. Returns
/// the element when the gcds are all 1, or else the divisor found (None
/// when there is none, all of n showing at once).
pub fn stage1<T: Clone>(n: &Integer, b1: u64, x: T, step: impl Fn(&T, &[u64]) -> T, test: impl Fn(&T) -> Integer) -> Result<T, Option<Integer>> {
    let mut x = x;
    let mut words: Vec<u64> = Vec::with_capacity(CHUNK);
    // The primes and prime powers of the chunk, to go again one at a time.
    let mut powers: Vec<(u64, u64)> = Vec::new();
    let mut word = 1u64;
    let mut out = None;
    let check = |x: &mut T, words: &mut Vec<u64>, powers: &mut Vec<(u64, u64)>| -> Option<Option<Integer>> {
        let start = x.clone();
        *x = step(x, words);
        let g = test(x);
        let found = if g.is_one() {
            None
        } else if g != *n {
            Some(Some(g))
        } else {
            Some(separate(n, start, powers, &step, &test))
        };
        words.clear();
        powers.clear();
        found
    };
    each_prime(2, b1, &mut |p| {
        let mut q = p;
        while q <= b1 / p {
            q *= p;
        }
        if word.checked_mul(q).is_none_or(|w| w >> 63 != 0) {
            words.push(word);
            word = 1;
            if words.len() == CHUNK {
                if let Some(r) = check(&mut x, &mut words, &mut powers) {
                    out = Some(r);
                    return false;
                }
            }
        }
        word *= q;
        powers.push((p, q));
        true
    });
    if let Some(r) = out {
        return Err(r);
    }
    if word > 1 {
        words.push(word);
    }
    match check(&mut x, &mut words, &mut powers) {
        Some(r) => Err(r),
        None => Ok(x),
    }
}

/// The primes of a chunk in turn, each one power at a time, until the gcd
/// is no longer 1: a proper divisor, or none when it jumps to n.
fn separate<T>(n: &Integer, mut x: T, powers: &[(u64, u64)], step: &impl Fn(&T, &[u64]) -> T, test: &impl Fn(&T) -> Integer) -> Option<Integer> {
    for &(p, q) in powers {
        let mut pk = 1;
        while pk < q {
            x = step(&x, &[p]);
            pk *= p;
            let g = test(&x);
            if !g.is_one() {
                return (g != *n).then_some(g);
            }
        }
    }
    None
}
