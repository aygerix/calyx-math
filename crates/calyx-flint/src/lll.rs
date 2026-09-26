//! LLL reduction of integer lattices by FLINT (`fmpz_lll`).

use flint3_sys as sys;

use crate::Integer;

/// Reduces the lattice spanned by `rows`, all of one length, in place: LLL
/// with FLINT's defaults (δ = 0.99, η = 0.51).
pub fn lll(rows: &mut [Vec<Integer>]) {
    lll_with(rows, 0.99);
}

/// LLL with η = 0.51 and the given δ, above η² and below 1: a smaller δ
/// reduces less but sooner, and a basis reduced with it is quick to reduce
/// further.
pub fn lll_with(rows: &mut [Vec<Integer>], delta: f64) {
    assert!(0.2601 < delta && delta < 1.0, "δ in (η², 1)");
    let (r, c) = (rows.len(), rows.first().map_or(0, |v| v.len()));
    if r == 0 || c == 0 {
        return;
    }
    assert!(rows.iter().all(|v| v.len() == c), "rows of one length");
    unsafe {
        let mut m: sys::fmpz_mat_struct = std::mem::zeroed();
        let mut fl: sys::fmpz_lll_struct = std::mem::zeroed();
        sys::fmpz_mat_init(&mut m, r as sys::slong, c as sys::slong);
        for (i, v) in rows.iter().enumerate() {
            for (j, x) in v.iter().enumerate() {
                sys::fmpz_set(sys::fmpz_mat_entry(&m, i as sys::slong, j as sys::slong), x.raw_ptr());
            }
        }
        sys::fmpz_lll_context_init(&mut fl, delta, 0.51, sys::rep_type_Z_BASIS, sys::gram_type_APPROX);
        sys::fmpz_lll(&mut m, std::ptr::null_mut(), &fl);
        // The reduced entries move out; the old ones are cleared with m.
        for (i, v) in rows.iter_mut().enumerate() {
            for (j, x) in v.iter_mut().enumerate() {
                sys::fmpz_swap(x.raw_mut_ptr(), sys::fmpz_mat_entry(&m, i as sys::slong, j as sys::slong));
            }
        }
        sys::fmpz_mat_clear(&mut m);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn int(v: i64) -> Integer {
        Integer::from_i64(v)
    }

    #[test]
    fn reduces_a_small_basis() {
        let mut rows = vec![vec![int(1), int(1), int(1)], vec![int(-1), int(0), int(2)], vec![int(3), int(5), int(6)]];
        lll(&mut rows);
        let norms: Vec<i64> = rows.iter().map(|v| v.iter().map(|x| x.to_i64().unwrap().pow(2)).sum()).collect();
        assert_eq!(norms, vec![1, 2, 5]);
    }

    #[test]
    fn finds_a_short_vector() {
        // The vectors (x, y) with x = 123456789 y mod n: the first one of a
        // reduced basis is within the 2-dimensional bound of sqrt(n).
        let n = int(1_000_000_007);
        let mut rows = vec![vec![n.clone(), int(0)], vec![int(123456789), int(1)]];
        lll(&mut rows);
        let first: Vec<i64> = rows[0].iter().map(|x| x.to_i64().unwrap()).collect();
        let (a, b) = (first[0], first[1]);
        assert_eq!((a - 123456789 * b).rem_euclid(1_000_000_007), 0);
        assert!(a * a + b * b < 2 * 1_000_000_007);
    }
}
