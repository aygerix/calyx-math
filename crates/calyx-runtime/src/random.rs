//! The pseudo-random generator behind `Random`, `SetSeed` and `GetSeed`.
//!
//! State is described by a seed and the number of steps taken since
//! seeding, so `SetSeed(s, c)` can reproduce any earlier state.

use calyx_flint::Integer;

pub struct Rng {
    seed: u64,
    steps: u64,
    state: [u64; 4],
}

fn splitmix(x: &mut u64) -> u64 {
    *x = x.wrapping_add(0x9e3779b97f4a7c15);
    let mut z = *x;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
    z ^ (z >> 31)
}

impl Rng {
    pub fn new(seed: u64) -> Rng {
        let mut s = seed;
        let state = [splitmix(&mut s), splitmix(&mut s), splitmix(&mut s), splitmix(&mut s)];
        Rng { seed, steps: 0, state }
    }

    pub fn from_time() -> Rng {
        let t = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_nanos() as u64).unwrap_or(1);
        Rng::new((t ^ (std::process::id() as u64).rotate_left(32)) % (1 << 32))
    }

    pub fn seed(&self) -> (u64, u64) {
        (self.seed, self.steps)
    }

    pub fn set_seed(&mut self, seed: u64, steps: u64) {
        *self = Rng::new(seed);
        for _ in 0..steps {
            self.raw();
        }
        self.steps = steps;
    }

    fn raw(&mut self) -> u64 {
        // xoshiro256**
        let s = &mut self.state;
        let result = s[1].wrapping_mul(5).rotate_left(7).wrapping_mul(9);
        let t = s[1] << 17;
        s[2] ^= s[0];
        s[3] ^= s[1];
        s[1] ^= s[2];
        s[0] ^= s[3];
        s[2] ^= t;
        s[3] = s[3].rotate_left(45);
        result
    }

    pub fn next_u64(&mut self) -> u64 {
        self.steps += 1;
        self.raw()
    }

    /// Uniform integer in `[0, n)` for `n > 0`.
    pub fn below_u64(&mut self, n: u64) -> u64 {
        assert!(n > 0);
        let zone = u64::MAX - (u64::MAX % n);
        loop {
            let r = self.next_u64();
            if r < zone {
                return r % n;
            }
        }
    }

    /// Uniform integer in `[0, n)` for `n > 0`.
    pub fn below(&mut self, n: &Integer) -> Integer {
        if let Some(small) = n.to_u64() {
            return Integer::from_u64(self.below_u64(small));
        }
        let bits = n.bits();
        let limbs = bits.div_ceil(64) as usize;
        let top_mask = if bits % 64 == 0 { u64::MAX } else { (1u64 << (bits % 64)) - 1 };
        loop {
            let mut v: Vec<u64> = (0..limbs).map(|_| self.next_u64()).collect();
            if let Some(last) = v.last_mut() {
                *last &= top_mask;
            }
            let r = Integer::from_limbs(&v, false);
            if &r < n {
                return r;
            }
        }
    }

    /// Uniform integer in `[a, b]`; requires `a <= b`.
    pub fn range(&mut self, a: &Integer, b: &Integer) -> Integer {
        let span = &(b - a) + &Integer::one();
        a + &self.below(&span)
    }
}
