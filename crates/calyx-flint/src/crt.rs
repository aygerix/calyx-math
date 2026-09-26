//! Chinese remaindering by FLINT's product tree, for many sets of residues
//! modulo one list of word moduli.

use flint3_sys as sys;

use crate::Integer;

/// A list of pairwise coprime word moduli, with FLINT's precomputed tree for
/// combining residues modulo them.
pub struct Crt {
    raw: Box<sys::fmpz_multi_CRT_struct>,
    len: usize,
    modulus: Integer,
}

impl Crt {
    /// For pairwise coprime moduli from 2 to 2^62; None for others or for
    /// none.
    pub fn new(moduli: &[u64]) -> Option<Crt> {
        if moduli.is_empty() || moduli.iter().any(|&m| !(2..1 << 62).contains(&m)) {
            return None;
        }
        // Below 2^62 an fmpz is the value itself.
        let ms: Vec<sys::fmpz> = moduli.iter().map(|&m| m as sys::fmpz).collect();
        let mut raw: Box<sys::fmpz_multi_CRT_struct> = Box::new(unsafe { std::mem::zeroed() });
        unsafe { sys::fmpz_multi_CRT_init(raw.as_mut()) };
        let ok = unsafe { sys::fmpz_multi_CRT_precompute(raw.as_mut(), ms.as_ptr(), ms.len() as sys::slong) } != 0;
        let mut modulus = Integer::zero();
        unsafe { sys::fmpz_set(modulus.raw_mut_ptr(), raw.final_modulus.as_ptr()) };
        let crt = Crt { raw, len: moduli.len(), modulus };
        ok.then_some(crt)
    }

    /// The product of the moduli.
    pub fn modulus(&self) -> &Integer {
        &self.modulus
    }

    /// The integer of least absolute value with the residues `r`, one for
    /// each modulus and each below it.
    pub fn combine(&self, r: &[u64]) -> Integer {
        assert_eq!(r.len(), self.len);
        let rs: Vec<sys::fmpz> = r.iter().map(|&x| x.min((1 << 62) - 1) as sys::fmpz).collect();
        let mut out = Integer::zero();
        unsafe { sys::fmpz_multi_CRT_precomp(out.raw_mut_ptr(), self.raw.as_ref(), rs.as_ptr(), 1) };
        out
    }
}

impl Drop for Crt {
    fn drop(&mut self) {
        unsafe { sys::fmpz_multi_CRT_clear(self.raw.as_mut()) };
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn residues_combine_to_the_integer() {
        let primes = [2147483647u64, 2147483629, 2147483587, 1000003, 7];
        let crt = Crt::new(&primes).unwrap();
        assert_eq!(*crt.modulus(), primes.iter().fold(Integer::one(), |m, &p| &m * p as i64));
        for s in ["0", "1", "-1", "123456789012345678901234567890", "-98765432109876543210987654321"] {
            let x = Integer::parse(s).unwrap();
            let r: Vec<u64> = primes.iter().map(|&p| x.mod_u64(p)).collect();
            assert_eq!(crt.combine(&r), x);
        }
        assert!(Crt::new(&[6, 4]).is_none());
        assert!(Crt::new(&[]).is_none());
    }
}
