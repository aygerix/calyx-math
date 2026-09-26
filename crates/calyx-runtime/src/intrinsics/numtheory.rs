//! Primes, modular arithmetic, residue symbols, norm equations and
//! Dickman's rho function.

use calyx_flint::{Integer, Real};

use super::{arg_ge, arg_le, arg_prime, boolv, intv, one};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::value::*;

/// `x mod m` in `[0, m)` for `m > 0`.
pub fn modp(x: &Integer, m: &Integer) -> Integer {
    x.fdiv_qr(m).unwrap().1
}

// ----- primes -------------------------------------------------------------------

/// Primality as the `Proof` parameter asks for (negatives of primes are
/// prime too).
fn prime_test(n: &Integer, proof: bool) -> bool {
    if proof { n.is_prime() } else { n.is_probable_prime() }
}

fn proof(a: &CallArgs) -> bool {
    !matches!(a.param("Proof"), Some(Value::Bool(false)))
}

fn is_prime(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(prime_test(a.int(0)?, proof(a)))
}

fn is_probable_prime(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(a.int(0)?.is_probable_prime())
}

fn is_prime_power(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int_ge(0, 2)?;
    let (b, e) = n.perfect_power().unwrap_or((n.clone(), 1));
    // b^e with e largest; b is then prime if n is a prime power.
    if b.is_prime() {
        return Ok(vals![Value::Bool(true), Value::Int(b), Value::Int(Integer::from_u64(e))]);
    }
    Ok(vals![Value::Bool(false), Value::Undef, Value::Undef])
}

fn next_prime(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int_ge(0, 0)?;
    if proof(a) {
        return intv(n.next_prime());
    }
    let mut p = &n + 1;
    while !p.is_probable_prime() {
        p = &p + 1;
    }
    intv(p)
}

fn previous_prime(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(a.int_ge(0, 3)?.previous_prime().unwrap())
}

/// Calls `f` with the primes in `[lo, hi]` in increasing order until it
/// returns false. A segmented sieve of Eratosthenes over the odd numbers,
/// with memory proportional to sqrt(hi); `hi` must be below 2^62.
pub fn each_prime(lo: u64, hi: u64, f: &mut dyn FnMut(u64) -> bool) {
    if hi < 2 || lo > hi {
        return;
    }
    if lo <= 2 && !f(2) {
        return;
    }
    let mut base = Vec::new();
    each_prime(3, hi.isqrt(), &mut |p| {
        base.push(p);
        true
    });
    // Each segment holds SEG odd numbers, from `start` on.
    const SEG: u64 = 1 << 18;
    let mut sieve = vec![false; SEG as usize];
    let mut start = lo.max(3) | 1;
    while start <= hi {
        let end = (start + 2 * (SEG - 1)).min(hi);
        let len = ((end - start) / 2 + 1) as usize;
        sieve[..len].fill(false);
        for &p in &base {
            if p * p > end {
                break;
            }
            let mut m = start.div_ceil(p).max(p) * p;
            if m % 2 == 0 {
                m += p;
            }
            let mut j = ((m - start) / 2) as usize;
            while j < len {
                sieve[j] = true;
                j += p as usize;
            }
        }
        for (j, &composite) in sieve[..len].iter().enumerate() {
            if !composite && !f(start + 2 * j as u64) {
                return;
            }
        }
        start += 2 * SEG;
    }
}

/// The primes up to `n`.
pub fn primes_up_to(n: u64) -> Vec<u64> {
    let mut out = Vec::new();
    each_prime(2, n, &mut |p| {
        out.push(p);
        true
    });
    out
}

fn primes_up_to_fn(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(0)?;
    if n.sign() <= 0 {
        return Err(RuntimeError::runtime("Limit must be positive"));
    }
    let n = n.to_u64().filter(|&n| n < 1 << 30).ok_or_else(|| RuntimeError::runtime("Limit is too large"))?;
    let mut out = Vec::new();
    each_prime(2, n, &mut |p| {
        out.push(Integer::from_u64(p));
        true
    });
    one(Value::int_seq(out))
}

fn primes_in_interval(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (lo, hi) = (a.int(0)?.clone(), a.int(1)?.clone());
    if hi < lo {
        return Err(RuntimeError::runtime("Upper limit < Lower Limit !"));
    }
    if hi.sign() <= 0 {
        return Err(RuntimeError::runtime("Upper limit must be positive"));
    }
    if lo.sign() <= 0 {
        return Err(RuntimeError::runtime("Lower limit must be positive"));
    }
    let hi = hi.to_u64().filter(|&h| h < 1 << 57).ok_or_else(|| RuntimeError::runtime("Limits are too large"))?;
    let lo = lo.to_u64().unwrap().max(2);
    if hi + 1 >= lo + (1 << 30) {
        return Err(RuntimeError::runtime("Interval is too large"));
    }
    let mut out = Vec::new();
    if hi.saturating_sub(lo) < hi.isqrt() / 64 {
        // A short interval high up: cheaper than sieving by every prime
        // below sqrt(hi).
        let hi = Integer::from_u64(hi);
        let mut p = Integer::from_u64(lo - 1).next_prime();
        while p <= hi {
            out.push(p.clone());
            p = p.next_prime();
        }
    } else {
        each_prime(lo, hi, &mut |p| {
            out.push(Integer::from_u64(p));
            true
        });
    }
    one(Value::int_seq(out))
}

/// pi(k 10^7), the number of primes up to k 10^7, for k = 1 .. 1000 (a row
/// per 10^8).
#[rustfmt::skip]
const PRIME_COUNTS: [u32; 1000] = [
    664579, 1270607, 1857859, 2433654, 3001134, 3562115, 4118064, 4669382, 5216954, 5761455,
    6303309, 6841648, 7378187, 7912199, 8444396, 8974458, 9503083, 10030385, 10555473, 11078937,
    11601626, 12122540, 12642573, 13161544, 13679318, 14195860, 14711384, 15226069, 15739663, 16252325,
    16764521, 17275206, 17785475, 18294605, 18803526, 19311288, 19818405, 20325373, 20831210, 21336326,
    21840713, 22344479, 22848050, 23350555, 23853038, 24354548, 24855718, 25356424, 25856368, 26355867,
    26854252, 27352687, 27850698, 28348381, 28845356, 29342150, 29838286, 30334175, 30829544, 31324703,
    31819444, 32313388, 32807229, 33300450, 33793395, 34286170, 34778319, 35270167, 35761747, 36252931,
    36743905, 37234048, 37724170, 38213987, 38703181, 39192219, 39680979, 40169476, 40658253, 41146179,
    41634187, 42121502, 42608404, 43095410, 43581966, 44067840, 44553888, 45039361, 45524412, 46009215,
    46494557, 46979583, 47463433, 47947424, 48431471, 48915316, 49398798, 49881580, 50364709, 50847534,
    51329983, 51812321, 52294318, 52776212, 53257350, 53738557, 54219990, 54700635, 55181788, 55662470,
    56142903, 56622753, 57102236, 57581414, 58060275, 58539733, 59019102, 59498032, 59976241, 60454705,
    60932761, 61411047, 61888328, 62366021, 62843676, 63320966, 63798708, 64275439, 64752124, 65228333,
    65705361, 66181282, 66657104, 67133252, 67609216, 68085138, 68560537, 69035407, 69510341, 69985473,
    70459856, 70934626, 71409034, 71883002, 72357409, 72831347, 73304900, 73779064, 74252677, 74726528,
    75199715, 75672734, 76146047, 76618438, 77091082, 77563693, 78035499, 78507915, 78979967, 79451833,
    79923617, 80394795, 80866553, 81338327, 81809269, 82279850, 82750863, 83221805, 83692860, 84163019,
    84633952, 85104323, 85574438, 86044101, 86514020, 86984006, 87453575, 87923092, 88392508, 88862422,
    89331502, 89800273, 90269041, 90737943, 91206350, 91674904, 92143195, 92611517, 93079603, 93547928,
    94015751, 94483423, 94950995, 95418606, 95886225, 96353875, 96821037, 97288440, 97755641, 98222287,
    98689899, 99156962, 99623163, 100089871, 100556393, 101022313, 101488558, 101954626, 102420732, 102886526,
    103352849, 103818920, 104283918, 104748778, 105214609, 105679943, 106145123, 106610598, 107075254, 107540122,
    108004655, 108469335, 108934016, 109398471, 109862949, 110327311, 110792152, 111256651, 111720807, 112184940,
    112648396, 113112027, 113575726, 114039346, 114502477, 114965865, 115429202, 115892315, 116355501, 116818447,
    117281057, 117743893, 118206828, 118669628, 119131774, 119594385, 120056675, 120519295, 120981472, 121443371,
    121905534, 122367757, 122829801, 123291907, 123753846, 124215747, 124677602, 125139201, 125600658, 126062167,
    126522860, 126984098, 127445024, 127905890, 128366505, 128827456, 129288064, 129748884, 130209594, 130670192,
    131130716, 131591207, 132050748, 132510959, 132970642, 133430688, 133890653, 134350870, 134810676, 135270258,
    135730230, 136189857, 136649664, 137108741, 137568157, 138027607, 138487092, 138946190, 139405198, 139864011,
    140323164, 140781724, 141240780, 141699446, 142158287, 142616407, 143075092, 143533218, 143991726, 144449537,
    144907436, 145365732, 145823350, 146281749, 146739737, 147197715, 147655871, 148113825, 148571420, 149028641,
    149485685, 149943346, 150401039, 150857976, 151315404, 151772733, 152230144, 152686986, 153143966, 153600805,
    154058111, 154514452, 154971154, 155427781, 155884247, 156341328, 156797046, 157253442, 157709870, 158165829,
    158622185, 159078766, 159534856, 159990891, 160446746, 160902119, 161358024, 161813919, 162269712, 162725196,
    163180838, 163636385, 164092483, 164547484, 165003087, 165458356, 165914057, 166369097, 166824245, 167279333,
    167734768, 168189772, 168644709, 169099647, 169554450, 170009652, 170464191, 170918408, 171372981, 171827136,
    172281569, 172735825, 173190593, 173644810, 174099561, 174553468, 175007697, 175462084, 175915686, 176369517,
    176823245, 177277397, 177731576, 178185476, 178639090, 179092527, 179546259, 179999595, 180452903, 180906194,
    181359670, 181813260, 182266343, 182719482, 183171976, 183624944, 184078254, 184531078, 184984095, 185436625,
    185889713, 186341803, 186794319, 187247261, 187700003, 188152389, 188605017, 189057071, 189509388, 189961812,
    190413921, 190865713, 191317917, 191769865, 192221866, 192674189, 193126079, 193577541, 194029285, 194481069,
    194932949, 195385047, 195836979, 196288511, 196739921, 197191474, 197642404, 198093391, 198544921, 198996103,
    199447993, 199899187, 200350257, 200801127, 201252464, 201703150, 202154025, 202605640, 203056468, 203507248,
    203957339, 204408535, 204859369, 205310587, 205760898, 206211936, 206662436, 207113325, 207563444, 208013454,
    208463895, 208914491, 209364672, 209814524, 210264343, 210714629, 211164335, 211614038, 212063834, 212514323,
    212964050, 213414045, 213863874, 214313933, 214763264, 215212942, 215663027, 216112172, 216561540, 217011319,
    217460710, 217909830, 218359494, 218808288, 219257904, 219706926, 220155938, 220605367, 221054879, 221504167,
    221952693, 222402080, 222850731, 223299672, 223748679, 224197950, 224646209, 225094454, 225543235, 225991743,
    226440279, 226889153, 227337210, 227785782, 228233908, 228682262, 229130248, 229578835, 230027299, 230475545,
    230923732, 231371447, 231819652, 232267781, 232715697, 233163925, 233611460, 234059567, 234507018, 234954223,
    235402317, 235850709, 236298538, 236745944, 237192977, 237640569, 238087645, 238535485, 238982982, 239429993,
    239877562, 240325158, 240772583, 241219434, 241666824, 242114200, 242560939, 243008278, 243455193, 243902342,
    244349528, 244796302, 245243217, 245689929, 246137111, 246583724, 247030611, 247476896, 247924223, 248370960,
    248817032, 249263667, 249709998, 250156133, 250602749, 251049626, 251495687, 251941966, 252387921, 252834065,
    253279954, 253726638, 254172495, 254618278, 255064623, 255511139, 255956897, 256403076, 256848672, 257294520,
    257740321, 258185887, 258631476, 259077372, 259522712, 259968906, 260414524, 260860406, 261306311, 261751864,
    262197348, 262643206, 263088815, 263534080, 263979672, 264424721, 264870531, 265316117, 265761344, 266206294,
    266651499, 267097010, 267541627, 267986753, 268431921, 268876642, 269321584, 269766462, 270211000, 270655552,
    271100430, 271545184, 271989736, 272434728, 272879197, 273323695, 273768442, 274213394, 274657243, 275101551,
    275546433, 275990412, 276434878, 276879261, 277323618, 277767865, 278211989, 278656596, 279101248, 279545368,
    279989498, 280433194, 280877067, 281321028, 281764467, 282208669, 282653053, 283096811, 283540763, 283984956,
    284428341, 284872062, 285316880, 285760491, 286204393, 286647732, 287091408, 287535302, 287978719, 288422869,
    288866207, 289309471, 289752512, 290196290, 290638942, 291082525, 291525405, 291969323, 292412923, 292856421,
    293299408, 293742520, 294185334, 294628209, 295071171, 295513620, 295956986, 296399970, 296842737, 297285198,
    297728155, 298170472, 298613457, 299055583, 299498597, 299940834, 300383275, 300826102, 301268592, 301711468,
    302154236, 302597506, 303040129, 303482963, 303925014, 304367059, 304809619, 305252230, 305694615, 306137611,
    306579563, 307021840, 307464156, 307906460, 308348380, 308790578, 309232369, 309674629, 310116933, 310558733,
    311000837, 311441946, 311884384, 312325753, 312767892, 313210073, 313651741, 314094037, 314535650, 314977166,
    315418544, 315860260, 316302200, 316743574, 317184818, 317626340, 318067250, 318508791, 318949699, 319391721,
    319833356, 320274584, 320715760, 321157027, 321598132, 322039072, 322480567, 322921782, 323362776, 323804352,
    324245013, 324686340, 325127822, 325568511, 326009984, 326451357, 326892245, 327333302, 327774255, 328215206,
    328655714, 329096126, 329537545, 329978291, 330418503, 330859120, 331299844, 331740085, 332180593, 332620900,
    333061551, 333501817, 333942552, 334382628, 334823246, 335263562, 335704631, 336144845, 336584689, 337024801,
    337465144, 337905467, 338346143, 338786763, 339226890, 339666582, 340106964, 340546112, 340986292, 341426904,
    341867437, 342307939, 342747532, 343187519, 343627495, 344067573, 344507360, 344946822, 345386661, 345826612,
    346266525, 346706305, 347145935, 347585429, 348024829, 348464555, 348904337, 349343235, 349782719, 350221825,
    350660947, 351100470, 351540412, 351979699, 352418713, 352858094, 353297600, 353736940, 354176008, 354615116,
    355054060, 355493691, 355932823, 356371983, 356810818, 357249986, 357689637, 358128746, 358567825, 359006517,
    359445666, 359884623, 360324245, 360763456, 361202528, 361640974, 362080016, 362518407, 362957228, 363395981,
    363835616, 364273767, 364712494, 365151267, 365589973, 366028777, 366467380, 366906424, 367345127, 367783654,
    368222975, 368661394, 369099728, 369537908, 369976305, 370414747, 370853094, 371292089, 371730337, 372168766,
    372606844, 373045128, 373483095, 373920912, 374359417, 374797255, 375235643, 375673159, 376111350, 376549859,
    376988534, 377426808, 377864667, 378302853, 378740664, 379178798, 379616823, 380055276, 380493210, 380930729,
    381368884, 381806239, 382243693, 382681786, 383119592, 383557425, 383995604, 384432893, 384870547, 385307831,
    385745566, 386183064, 386620895, 387058481, 387495567, 387932553, 388370251, 388807300, 389245143, 389682427,
    390119805, 390557244, 390994597, 391431941, 391869505, 392306908, 392744451, 393181188, 393618651, 394055910,
    394493344, 394929906, 395367104, 395804111, 396241168, 396677947, 397114589, 397551432, 397988098, 398425675,
    398862704, 399299619, 399736387, 400173371, 400609733, 401046392, 401482809, 401919503, 402356634, 402793457,
    403230160, 403666816, 404103586, 404540419, 404977223, 405413862, 405850184, 406286599, 406723082, 407159590,
    407595743, 408031862, 408468626, 408905053, 409341670, 409778054, 410213957, 410650724, 411086855, 411523195,
    411959593, 412396308, 412832797, 413268776, 413704686, 414140808, 414576945, 415013051, 415449257, 415885628,
    416321137, 416757730, 417193170, 417629513, 418065095, 418500866, 418936157, 419372554, 419807555, 420243162,
    420679919, 421115539, 421551781, 421987863, 422423529, 422859389, 423295932, 423731727, 424167836, 424603409,
    425038762, 425474642, 425910388, 426345737, 426781096, 427216474, 427651643, 428087100, 428522657, 428958595,
    429393801, 429829753, 430264876, 430700704, 431135989, 431570922, 432006429, 432441493, 432876425, 433311792,
    433746862, 434182284, 434617829, 435053030, 435487590, 435922762, 436358292, 436793079, 437228498, 437663672,
    438098777, 438533936, 438969530, 439404130, 439838701, 440274195, 440709621, 441144588, 441579782, 442014876,
    442450176, 442885035, 443319592, 443754571, 444189277, 444623668, 445058669, 445493360, 445927981, 446362736,
    446797715, 447232109, 447666563, 448101528, 448535702, 448970364, 449404711, 449839558, 450274050, 450708777,
    451142771, 451577154, 452011922, 452446384, 452880587, 453315090, 453749767, 454183531, 454618086, 455052511,
];

/// The nth prime, for 1 <= n <= pi(10^10).
fn nth_prime_of(n: u64) -> u64 {
    // It lies in (k 10^7, (k + 1) 10^7] for the k below.
    let k = PRIME_COUNTS.partition_point(|&c| (c as u64) < n) as u64;
    let mut left = n - if k == 0 { 0 } else { PRIME_COUNTS[k as usize - 1] as u64 };
    let mut found = 0;
    each_prime(k * 10_000_000 + 1, (k + 1) * 10_000_000, &mut |p| {
        left -= 1;
        found = p;
        left > 0
    });
    found
}

fn nth_prime(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int_ge(0, 0)?.to_u64().filter(|&n| n <= PRIME_COUNTS[999] as u64).ok_or_else(|| RuntimeError::runtime("Integer is too large"))?;
    intv(if n == 0 { Integer::one() } else { Integer::from_u64(nth_prime_of(n)) })
}

// ----- modular arithmetic --------------------------------------------------------

fn modexp(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (n, k, m) = (a.int(0)?.clone(), a.int(1)?.clone(), a.int(2)?.clone());
    if m.sign() <= 0 {
        return Err(arg_ge(3, &m, 2));
    }
    if m.is_one() {
        return intv(Integer::zero());
    }
    match n.powm(&k, &m) {
        Some(r) => intv(r),
        // Magma names the exponent as argument 1 here.
        None => Err(RuntimeError::runtime(format!("Argument 1 ({k}) has no inverse modulo argument 3 ({m})"))),
    }
}

fn modinv(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = a.int_ge(1, 1)?;
    if m.is_one() {
        return intv(Integer::zero());
    }
    match a.int(0)?.invmod(&m) {
        Some(r) => intv(r),
        None => Err(RuntimeError::runtime("Argument 1 is not a unit mod argument 2")),
    }
}

/// A square root of `n` modulo the odd prime `p` (Tonelli and Shanks, with
/// the least non-residue), for `n` a non-zero square.
fn sqrt_mod_prime(n: &Integer, p: &Integer) -> Integer {
    let one_ = Integer::one();
    let (mut q, mut s) = (p - 1, 0u64);
    while q.is_even() {
        q = q.fdiv_2exp(1);
        s += 1;
    }
    let mut z = Integer::from_i64(2);
    while z.kronecker(p) != -1 {
        z = &z + 1;
    }
    let mut m = s;
    let mut c = z.powm(&q, p).unwrap();
    let mut t = n.powm(&q, p).unwrap();
    let mut r = n.powm(&(&q + 1).fdiv_2exp(1), p).unwrap();
    while t != one_ {
        let (mut i, mut tt) = (0u64, t.clone());
        while tt != one_ {
            tt = modp(&(&tt * &tt), p);
            i += 1;
        }
        let b = c.powm(&Integer::one().mul_2exp(m - i - 1), p).unwrap();
        m = i;
        c = modp(&(&b * &b), p);
        t = modp(&(&t * &c), p);
        r = modp(&(&r * &b), p);
    }
    r
}

/// Whether `n` is a square modulo `p^k`.
pub fn is_square_mod_prime_power(n: &Integer, p: &Integer, k: u64) -> bool {
    let n = modp(n, &p.pow(k));
    if n.is_zero() {
        return true;
    }
    let (e, u) = n.remove(p);
    if e % 2 == 1 {
        return false;
    }
    if p.is_even() {
        let need = 1u64 << (k - e).min(3);
        u.mod_u64(need) == 1 % need
    } else {
        u.kronecker(p) == 1
    }
}

/// A square root of `n` modulo `p^k`, the one Magma chooses: the integer
/// square root when `n` (as an integer in `[0, p^k)`) is a perfect square,
/// and otherwise, for `n = p^(2s) u` with `u` a unit, `p^s` times the root
/// of `u` modulo `p^k`.
fn sqrt_mod_prime_power(n: &Integer, p: &Integer, k: u64) -> Option<Integer> {
    let m = p.pow(k);
    let n = modp(n, &m);
    if n.is_square() {
        return n.isqrt();
    }
    let (e, u) = n.remove(p);
    if e % 2 == 1 {
        return None;
    }
    let r = unit_sqrt_mod_prime_power(&u, p, k)?;
    Some(modp(&(&r * &p.pow(e / 2)), &m))
}

/// The square root Magma takes of a unit `u < p^k` modulo `p^k`. For odd
/// `p` it is the lift of the Tonelli–Shanks root modulo `p` (which
/// determines it). For `p = 2` it is where Magma's Newton iteration stops.
fn unit_sqrt_mod_prime_power(u: &Integer, p: &Integer, k: u64) -> Option<Integer> {
    let m = p.pow(k);
    if p.is_even() {
        if u.mod_u64(8) != 1 {
            return None;
        }
        if k <= 3 {
            return Some(modp(&Integer::one(), &m));
        }
        // x <- x - ((x^2 - u) mod 2^k) / 2 * x^-1 modulo 2^k, from
        // (u + 1) / 2 until x is fixed. Halving after the reduction loses
        // the top bit of x^2 - u, so which of the two roots that are 1 mod 4
        // it reaches depends on the path, and this path is Magma's.
        let mut x = (u + 1).fdiv_2exp(1);
        // A step takes a root modulo 2^j (j >= 3) to one modulo 2^(2j-2),
        // so about log2(k) steps reach 2^k.
        for _ in 0..=k {
            let d = modp(&(&(&x * &x) - u), &m);
            let next = modp(&(&x - &(&d.fdiv_2exp(1) * &x.invmod(&m)?)), &m);
            if next == x {
                return Some(x);
            }
            x = next;
        }
        unreachable!("Newton's iteration converges modulo 2^k");
    }
    if u.kronecker(p) != 1 {
        return None;
    }
    // Newton's iteration lifts the root modulo p to p^k.
    let two = Integer::from_i64(2);
    let mut r = sqrt_mod_prime(&modp(u, p), p);
    loop {
        let d = &(&r * &r) - u;
        if d.is_divisible_by(&m) {
            return Some(modp(&r, &m));
        }
        r = modp(&(&r - &(&d * &(&two * &r).invmod(&m)?)), &m);
    }
}

/// The square roots of a unit `u` modulo `p^j`: y and -y, and for p = 2
/// also y + 2^(j-1) and -y + 2^(j-1).
fn unit_sqrts_mod_prime_power(u: &Integer, p: &Integer, j: u64) -> Vec<Integer> {
    let m = p.pow(j);
    let Some(y) = sqrt_mod_prime_power(u, p, j) else { return Vec::new() };
    let neg = modp(&-&y, &m);
    let mut out = vec![y.clone(), neg.clone()];
    if *p == Integer::from_i64(2) && j >= 3 {
        let half = Integer::one().mul_2exp(j - 1);
        out.extend([modp(&(&y + &half), &m), modp(&(&neg + &half), &m)]);
    }
    out.dedup();
    out
}

/// All square roots of `n` modulo `p^k` in increasing order (at most
/// `limit` of them).
fn roots_mod_prime_power(n: &Integer, p: &Integer, k: u64, limit: usize) -> Vec<Integer> {
    // With n = p^v u (u a unit), a root is p^s y with v = 2s and y^2 = u
    // modulo p^(k-2s), and each such y gives p^s roots modulo p^k. When p^k
    // divides n the roots are the multiples of p^ceil(k/2).
    let m = p.pow(k);
    let nn = modp(n, &m);
    let (units, s) = if nn.is_zero() {
        (vec![Integer::zero()], k / 2)
    } else {
        let (v, u) = nn.remove(p);
        if v % 2 == 1 {
            return Vec::new();
        }
        (unit_sqrts_mod_prime_power(&u, p, k - v), v / 2)
    };
    let (ps, step) = (p.pow(s), p.pow(k - s));
    let mut all = Vec::new();
    'units: for y in &units {
        let mut x = &ps * y;
        for _ in 0..ps.to_u64().unwrap_or(u64::MAX) {
            if all.len() >= limit {
                break 'units;
            }
            all.push(modp(&x, &m));
            x = &x + &step;
        }
    }
    all.sort();
    all
}

/// The square roots of `n` modulo `p^k` (at most `limit` of them), the one
/// `sqrt_mod_prime_power` chooses first.
fn all_sqrt_mod_prime_power(n: &Integer, p: &Integer, k: u64, limit: usize) -> Vec<Integer> {
    let m = p.pow(k);
    let Some(r) = sqrt_mod_prime_power(n, p, k) else { return Vec::new() };
    let mut out = vec![r.clone()];
    if m.to_u64().is_some_and(|m| m <= 1 << 14) {
        // Small moduli: all roots by search.
        let nn = modp(n, &m);
        let mut x = Integer::zero();
        while x < m && out.len() < limit {
            if x != r && modp(&(&x * &x), &m) == nn {
                out.push(x.clone());
            }
            x = &x + 1;
        }
        return out;
    }
    let all = roots_mod_prime_power(n, p, k, limit);
    // The roots found before the others were enumerated keep their places.
    let neg = modp(&-&r, &m);
    let mut first = vec![neg.clone()];
    if *p == Integer::from_i64(2) && k >= 3 {
        let half = Integer::one().mul_2exp(k - 1);
        first.extend([modp(&(&r + &half), &m), modp(&(&neg + &half), &m)]);
    }
    for x in first.into_iter().chain(all) {
        if out.len() < limit && !out.contains(&x) {
            out.push(x);
        }
    }
    out
}

/// Square roots of `n` modulo `m`, Magma's choice first, then the others
/// (up to `limit` of them).
fn sqrts_mod(n: &Integer, m: &Integer, limit: usize) -> Vec<Integer> {
    let Some(first) = modsqrt(n, m) else { return Vec::new() };
    let Some(f) = m.factor() else { return vec![first] };
    let mut combos: Vec<(Integer, Integer)> = vec![(Integer::zero(), Integer::one())];
    for (p, k) in &f.factors {
        let pk = p.pow(*k);
        let roots = all_sqrt_mod_prime_power(n, p, *k, limit);
        let mut next = Vec::new();
        for (x, big) in &combos {
            for r in &roots {
                let t = modp(&(&(r - x) * &modp(big, &pk).invmod(&pk).unwrap_or_else(Integer::zero)), &pk);
                next.push((x + &(big * &t), big * &pk));
                if next.len() >= limit {
                    break;
                }
            }
        }
        combos = next;
    }
    let mut out = vec![first.clone()];
    for (x, big) in combos {
        let x = modp(&x, &big);
        if x != first && out.len() < limit {
            out.push(x);
        }
    }
    out
}

/// Magma's square root of `n` modulo `m > 1`.
pub fn modsqrt(n: &Integer, m: &Integer) -> Option<Integer> {
    let n = modp(n, m);
    if n.is_square() {
        return n.isqrt();
    }
    modsqrt_factored(&n, &m.factor()?.factors)
}

/// `x + big * t` with `t` chosen so that the result is `r` modulo `pk`
/// (`big` and `pk` coprime): one step of the Chinese remainder theorem.
fn crt_join(x: &Integer, big: &Integer, r: &Integer, pk: &Integer) -> Integer {
    let t = modp(&(&(r - x) * &modp(big, pk).invmod(pk).unwrap_or_else(Integer::zero)), pk);
    x + &(big * &t)
}

/// Magma's square root of `n` modulo the product of the prime powers `f`
/// (increasing primes).
pub fn modsqrt_factored(n: &Integer, f: &[(Integer, u64)]) -> Option<Integer> {
    let m = super::factseq::fact_int(f);
    let n = modp(n, &m);
    if n.is_square() {
        return n.isqrt();
    }
    let (mut x, mut big) = (Integer::zero(), Integer::one());
    for (p, k) in f {
        let pk = p.pow(*k);
        let r = sqrt_mod_prime_power(&n, p, *k)?;
        x = crt_join(&x, &big, &r, &pk);
        big = &big * &pk;
    }
    Some(modp(&x, &big))
}

/// Whether `n` is a square modulo the product of the prime powers `f`.
pub fn is_square_mod_factored(n: &Integer, f: &[(Integer, u64)]) -> bool {
    f.iter().all(|(p, k)| is_square_mod_prime_power(n, p, *k))
}

/// All square roots of `n` modulo the product of the prime powers `f`, in
/// increasing order; `None` if there are more than `limit`.
pub fn all_sqrts_factored(n: &Integer, f: &[(Integer, u64)], limit: usize) -> Option<Vec<Integer>> {
    let mut combos = vec![Integer::zero()];
    let mut big = Integer::one();
    for (p, k) in f {
        let pk = p.pow(*k);
        let roots = roots_mod_prime_power(n, p, *k, limit + 1);
        if roots.len().saturating_mul(combos.len()) > limit {
            return None;
        }
        combos = combos.iter().flat_map(|x| roots.iter().map(|r| crt_join(x, &big, r, &pk)).collect::<Vec<_>>()).collect();
        big = &big * &pk;
    }
    let mut out: Vec<Integer> = combos.iter().map(|x| modp(x, &big)).collect();
    out.sort();
    Some(out)
}

fn modsqrt_fn(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = a.int_ge(1, 2)?;
    match modsqrt(a.int(0)?, &m) {
        Some(r) => intv(r),
        None => Err(RuntimeError::runtime("Argument has no square root")),
    }
}

fn modorder_fn(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = a.int_ge(1, 2)?;
    intv(super::ints::modorder(a.int(0)?, &m))
}

fn is_primitive(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = a.int_ge(1, 2)?;
    let n = a.int_ge(0, 1)?;
    let top = &m - 1;
    if n > top {
        return Err(arg_le(1, &n, &top));
    }
    let order = super::ints::modorder(&n, &m);
    boolv(!order.is_zero() && order == m.euler_phi())
}

fn primitive_root(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = a.int_ge(0, 2)?;
    intv(super::ints::primitive_root(&m).unwrap_or_else(Integer::zero))
}

/// The solutions of `a x = b (mod m)` as `x0 + i*k`, if any.
pub fn linear_congruence(a: &Integer, b: &Integer, m: &Integer) -> Option<(Integer, Integer)> {
    let g = a.gcd(m);
    if !b.is_divisible_by(&g) {
        return None;
    }
    let k = m.divexact(&g);
    if k.is_one() {
        return Some((Integer::zero(), k));
    }
    let inv = modp(&a.divexact(&g), &k).invmod(&k)?;
    Some((modp(&(&b.divexact(&g) * &inv), &k), k))
}

fn solution(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = a.int_ge(2, 1)?;
    match linear_congruence(a.int(0)?, a.int(1)?, &m) {
        Some((x, k)) => Ok(vals![Value::Int(x), Value::Int(k)]),
        None => Ok(vals![Value::int(-1), Value::Undef]),
    }
}

/// `x = r (mod m)` combined with the congruences so far (moduli need not
/// be coprime).
fn crt_step(x: &Integer, big: &Integer, r: &Integer, m: &Integer) -> Option<(Integer, Integer)> {
    let (g, s, _) = big.xgcd(m);
    let diff = r - x;
    if !diff.is_divisible_by(&g) {
        return None;
    }
    let l = big.lcm(m);
    let step = &(big * &s) * &diff.divexact(&g);
    Some((modp(&(x + &step), &l), l))
}

fn int_elems(v: &Value) -> RResult<Vec<Integer>> {
    super::ints::ints_of(v)
}

fn crt(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(crt_of(&int_elems(&a.args[0])?, &int_elems(&a.args[1])?)?)
}

/// The least x >= 0 with x = xs[i] mod ms[i] for all i, or -1 if there is
/// none.
pub(super) fn crt_of(xs: &[Integer], ms: &[Integer]) -> RResult<Integer> {
    if xs.is_empty() {
        return Err(RuntimeError::runtime("Sequence argument 1 must be non-empty"));
    }
    if xs.len() != ms.len() {
        return Err(RuntimeError::runtime("Lengths of sequence arguments should be the same"));
    }
    if ms.iter().any(|m| m.is_zero()) {
        return Err(RuntimeError::runtime("Element of second argument (moduli M) is zero"));
    }
    let (mut x, mut big) = (Integer::zero(), Integer::one());
    for (r, m) in xs.iter().zip(ms) {
        match crt_step(&x, &big, r, &m.abs()) {
            Some((nx, nb)) => (x, big) = (nx, nb),
            None => return Ok(Integer::from_i64(-1)),
        }
    }
    Ok(x)
}

fn solution_seq(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (aa, bb, nn) = (int_elems(&a.args[0])?, int_elems(&a.args[1])?, int_elems(&a.args[2])?);
    if aa.len() != bb.len() || aa.len() != nn.len() {
        return Err(RuntimeError::runtime("Lengths of sequence arguments should be the same"));
    }
    let (mut x, mut big) = (Integer::zero(), Integer::one());
    for ((ai, bi), ni) in aa.iter().zip(&bb).zip(&nn) {
        if ni.sign() <= 0 {
            return Err(RuntimeError::runtime("Moduli must be positive"));
        }
        let Some((r, k)) = linear_congruence(ai, bi, ni) else {
            return intv(Integer::from_i64(-1));
        };
        match crt_step(&x, &big, &r, &k) {
            Some((nx, nb)) => (x, big) = (nx, nb),
            None => return intv(Integer::from_i64(-1)),
        }
    }
    intv(x)
}

// ----- residue symbols -------------------------------------------------------------

fn legendre(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let p = a.int_ge(1, 3)?;
    if !p.is_prime() {
        return Err(arg_prime(2, &p));
    }
    one(Value::int(a.int(0)?.kronecker(&p) as i64))
}

fn jacobi(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int_ge(1, 3)?;
    if n.is_even() {
        return Err(RuntimeError::runtime(format!("Argument 2 ({n}) should not be divisible by 2")));
    }
    one(Value::int(a.int(0)?.kronecker(&n) as i64))
}

fn kronecker(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::int(a.int(0)?.kronecker(a.int(1)?) as i64))
}

// ----- norm equations ----------------------------------------------------------------

/// Cornacchia's algorithm: x^2 + d y^2 = m from a square root r0 of -d
/// modulo m.
fn cornacchia(d: &Integer, m: &Integer, r0: &Integer) -> Option<(Integer, Integer)> {
    let lim = m.isqrt()?;
    let (mut a, mut b) = (m.clone(), r0.clone());
    while b > lim {
        let r = modp(&a, &b);
        a = b;
        b = r;
    }
    let t = m - &(&b * &b);
    if !t.is_divisible_by(d) {
        return None;
    }
    let y2 = t.divexact(d);
    if !y2.is_square() {
        return None;
    }
    Some((b, y2.isqrt()?))
}

/// Non-negative x, y with x^2 + d y^2 = m, as Magma finds them.
pub fn norm_equation(d: &Integer, m: &Integer) -> Option<(Integer, Integer)> {
    if m.is_zero() {
        return Some((Integer::zero(), Integer::zero()));
    }
    if m.is_one() {
        return Some(if d.is_one() { (Integer::zero(), Integer::one()) } else { (Integer::one(), Integer::zero()) });
    }
    // When gcd(d, m) is a square h^2, h divides x: solve x'^2 + (d/h^2) y^2 = m/h^2.
    let c = d.gcd(m);
    if !c.is_one() && c.is_square() {
        let (x, y) = norm_equation(&d.divexact(&c), &m.divexact(&c))?;
        return Some((&x * &c.isqrt()?, y));
    }
    if m.is_square() {
        return Some((m.isqrt()?, Integer::zero()));
    }
    // Cornacchia modulo m / g^2 for g^2 | m, from g = 1 up, over the square
    // roots of -d in increasing order (r and m - r lead to the same solution).
    let f = m.factor()?;
    let mut gs = super::factseq::divisors_of(&f.factors.iter().filter(|(_, e)| *e >= 2).map(|(p, e)| (p.clone(), e / 2)).collect());
    gs.sort();
    for g in gs {
        let mm = m.divexact(&(&g * &g));
        let mut roots = sqrts_mod(&-d, &mm, 1 << 20);
        roots.sort();
        for r0 in roots {
            if let Some((x, y)) = cornacchia(d, &mm, &r0) {
                return Some((&x * &g, &y * &g));
            }
        }
    }
    None
}

fn norm_equation_fn(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (d, m) = (a.int(0)?.clone(), a.int(1)?.clone());
    if d.sign() <= 0 || m.sign() < 0 {
        return Err(RuntimeError::runtime("Argument 1 must be positive and argument 2 non-negative"));
    }
    match norm_equation(&d, &m) {
        Some((x, y)) => Ok(vals![Value::Bool(true), Value::Int(x), Value::Int(y)]),
        None => Ok(vals![Value::Bool(false), Value::Undef, Value::Undef]),
    }
}

// ----- Dickman's rho ------------------------------------------------------------------

/// rho(u) to `target` bits: on [k-1, k] rho(k - z) is a power
/// series in z whose coefficients follow from those on [k-2, k-1] by
/// u rho'(u) = -rho(u - 1).
fn dickman_rho(u: &Real, target: u64) -> Real {
    let bits = target + 64;
    let one_ = Real::from_integer(&Integer::one(), bits);
    if u.sub(&one_).sign() <= 0 {
        return one_.round_to(target);
    }
    let k = u.ceil();
    let kk = k.to_u64().unwrap_or(u64::MAX);
    let terms = bits as usize + 40;
    let mut c: Vec<Real> = (0..terms).map(|j| if j == 0 { one_.clone() } else { Real::zero(bits) }).collect();
    for i in 2..=kk {
        let ki = Integer::from_u64(i);
        let mut next = vec![Real::zero(bits); terms];
        for j in 0..terms - 1 {
            let num = c[j].add(&next[j].mul(&Real::from_integer(&Integer::from_u64(j as u64), bits)));
            next[j + 1] = num.div(&Real::from_integer(&(&ki * &Integer::from_u64(j as u64 + 1)), bits)).unwrap();
        }
        // Continuity at u = i - 1 (z = 1) fixes the constant term.
        let mut s = Real::zero(bits);
        for x in &next[1..] {
            s = s.add(x);
        }
        next[0] = c[0].sub(&s);
        c = next;
    }
    let z = Real::from_integer(&k, bits).sub(&u.round_to(bits));
    let mut r = Real::zero(bits);
    for x in c.iter().rev() {
        r = r.mul(&z).add(x);
    }
    r.round_to(target)
}

fn dickman_rho_fn(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let target = match &a.args[0] {
        Value::Real(r) => r.x.prec(),
        _ => super::reals::default_bits(),
    };
    let u = super::reals::to_real(&a.args[0], target).unwrap().round_to(target + 64);
    one(Value::real(dickman_rho(&u, target)))
}

pub fn register(it: &mut Interp) {
    it.def_params("IsPrime", "n::RngIntElt -> BoolElt", &[("Proof", Value::Bool(true))], "Whether n is a prime number (or the negative of one).", is_prime);
    for name in ["IsProbablePrime", "IsProbablyPrime"] {
        it.def_params(name, "n::RngIntElt -> BoolElt", &[("Bases", Value::int(20))], "Whether |n| passes a strong probable-prime test.", is_probable_prime);
    }
    it.def("IsPrimePower", "n::RngIntElt -> BoolElt, RngIntElt, RngIntElt", "Whether n is a prime power p^k, and p and k.", is_prime_power);
    it.def_params("NextPrime", "n::RngIntElt -> RngIntElt", &[("Proof", Value::Bool(true))], "The least prime greater than n.", next_prime);
    it.def_params("PreviousPrime", "n::RngIntElt -> RngIntElt", &[("Proof", Value::Bool(true))], "The greatest prime less than n.", previous_prime);
    it.def("NthPrime", "n::RngIntElt -> RngIntElt", "The n-th prime (1 for n = 0).", nth_prime);
    it.def("PrimesUpTo", "n::RngIntElt -> [RngIntElt]", "The primes up to n.", primes_up_to_fn);
    it.def("PrimesInInterval", "a::RngIntElt, b::RngIntElt -> [RngIntElt]", "The primes in the interval [a, b].", primes_in_interval);

    it.def("Modexp", "n::RngIntElt, k::RngIntElt, m::RngIntElt -> RngIntElt", "n^k mod m.", modexp);
    for name in ["Modinv", "InverseMod"] {
        it.def(name, "n::RngIntElt, m::RngIntElt -> RngIntElt", "The inverse of n modulo m.", modinv);
    }
    it.def("Modsqrt", "n::RngIntElt, m::RngIntElt -> RngIntElt", "A square root of n modulo m.", modsqrt_fn);
    it.def("Modorder", "n::RngIntElt, m::RngIntElt -> RngIntElt", "The order of n modulo m, or 0 if n is not a unit modulo m.", modorder_fn);
    it.def("IsPrimitive", "n::RngIntElt, m::RngIntElt -> BoolElt", "Whether n is a primitive root modulo m.", is_primitive);
    it.def("PrimitiveRoot", "m::RngIntElt -> RngIntElt", "The least primitive root modulo m, or 0 if there is none.", primitive_root);
    it.def(
        "Solution",
        "a::RngIntElt, b::RngIntElt, m::RngIntElt -> RngIntElt, RngIntElt",
        "x0 and k such that the solutions of a*x = b mod m are x0 + i*k, or -1.",
        solution,
    );
    it.def(
        "Solution",
        "A::[RngIntElt], B::[RngIntElt], N::[RngIntElt] -> RngIntElt",
        "The least x >= 0 with A[i]*x = B[i] mod N[i] for all i, or -1.",
        solution_seq,
    );
    for name in ["CRT", "ChineseRemainderTheorem"] {
        it.def(name, "X::[RngIntElt], N::[RngIntElt] -> RngIntElt", "The least x >= 0 with x = X[i] mod N[i] for all i, or -1.", crt);
    }
    it.def("LegendreSymbol", "n::RngIntElt, p::RngIntElt -> RngIntElt", "The Legendre symbol (n/p) for an odd prime p.", legendre);
    it.def("JacobiSymbol", "n::RngIntElt, m::RngIntElt -> RngIntElt", "The Jacobi symbol (n/m) for odd m >= 3.", jacobi);
    it.def("KroneckerSymbol", "n::RngIntElt, m::RngIntElt -> RngIntElt", "The Kronecker symbol (n/m).", kronecker);
    it.def_params(
        "NormEquation",
        "d::RngIntElt, m::RngIntElt -> BoolElt, RngIntElt, RngIntElt",
        &[("Factorization", Value::seq(None, Vec::new()))],
        "Whether x^2 + d*y^2 = m has a solution, and non-negative x and y.",
        norm_equation_fn,
    );
    for t in ["RngIntElt", "FldRatElt", "FldReElt"] {
        it.def("DickmanRho", &format!("u::{t} -> FldReElt"), "Dickman's rho function at u.", dickman_rho_fn);
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;

    #[test]
    fn segmented_sieve_matches_trial_division() {
        let is_prime = |n: u64| n >= 2 && (2..).take_while(|d| d * d <= n).all(|d| n % d != 0);
        // The last range crosses a segment boundary.
        for (lo, hi) in [(0, 1000), (1, 2), (2, 2), (3, 3), (4, 4), (8, 9), (999_000, 1_001_000), (1 << 20, (1 << 20) + 600_000)] {
            let mut got = Vec::new();
            each_prime(lo, hi, &mut |p| {
                got.push(p);
                true
            });
            let want: Vec<u64> = (lo..=hi).filter(|&n| is_prime(n)).collect();
            assert_eq!(got, want, "primes in [{lo}, {hi}]");
        }
    }

    #[test]
    fn nth_prime_across_the_table() {
        assert_eq!(nth_prime_of(1), 2);
        assert_eq!(nth_prime_of(10), 29);
        assert_eq!(nth_prime_of(664579), 9999991);
        assert_eq!(nth_prime_of(664580), 10000019);
        assert_eq!(nth_prime_of(5761455), 99999989);
        assert_eq!(nth_prime_of(5761456), 100000007);
        assert_eq!(nth_prime_of(50847535), 1000000007);
    }

    #[test]
    fn square_roots_modulo_prime_powers_are_complete() {
        let roots = |n: u64, p: u64, k: u64| -> Vec<u64> {
            let mut r: Vec<u64> =
                all_sqrt_mod_prime_power(&Integer::from_u64(n), &Integer::from_u64(p), k, usize::MAX).iter().map(|x| x.to_u64().unwrap()).collect();
            r.sort();
            r
        };
        assert_eq!(roots(9, 3, 10), [3, 19680, 19686, 39363, 39369, 59046]);
        // Moduli above 2^14, where the roots are not found by search: every
        // residue for the first two, some for the others.
        for (p, k, all) in [(3u64, 10u64, true), (2, 15, true), (7, 5, false), (5, 7, false), (2, 16, false)] {
            let m = p.pow(k as u32);
            let mut squares: HashMap<u64, Vec<u64>> = HashMap::new();
            for x in 0..m {
                squares.entry(x * x % m).or_default().push(x);
            }
            let ns: Vec<u64> = if all { (0..m).collect() } else { vec![0, 1, 2, 4, 9, 17, p * p, 3 * p * p, p.pow(4), 2 * p.pow(4), m / p, m / (p * p)] };
            for n in ns {
                assert_eq!(roots(n % m, p, k), squares.get(&(n % m)).cloned().unwrap_or_default(), "x^2 = {n} mod {p}^{k}");
            }
        }
    }

    #[test]
    fn square_roots_modulo_powers_of_two_are_magmas() {
        // Magma 2.22's choices, which are not the 2-adic roots.
        let cases = [(17, 6, 9), (41, 6, 45), (49, 6, 7), (17, 7, 105), (41, 7, 13), (57, 8, 213), (17, 9, 233), (41, 9, 461)];
        for (n, k, r) in cases.into_iter().chain([(9876537, 40, 1016796945493)]) {
            let m = Integer::one().mul_2exp(k);
            assert_eq!(modsqrt(&Integer::from_u64(n), &m), Some(Integer::from_u64(r)), "Modsqrt({n}, 2^{k})");
        }
    }

    /// A xorshift generator, so that the cases are the same on every run.
    fn next(s: &mut u64) -> u64 {
        *s ^= *s << 13;
        *s ^= *s >> 7;
        *s ^= *s << 17;
        *s
    }

    fn int(v: i64) -> Integer {
        Integer::from_i64(v)
    }

    /// A random prime of at most `bits` bits.
    fn prime(s: &mut u64, bits: u32) -> Integer {
        Integer::from_u64(next(s) >> (64 - bits)).next_prime()
    }

    #[test]
    fn crt_finds_the_least_solution() {
        let mut s = 0x2545_f491_4f6c_dd1d;
        for _ in 0..3000 {
            let k = 1 + next(&mut s) as usize % 3;
            let ms: Vec<i64> = (0..k).map(|_| (1 + next(&mut s) % 24) as i64 * if next(&mut s) % 4 == 0 { -1 } else { 1 }).collect();
            let xs: Vec<i64> = (0..k).map(|_| (next(&mut s) % 101) as i64 - 50).collect();
            let l = ms.iter().fold(int(1), |l, &m| l.lcm(&int(m))).to_i64().unwrap();
            let want = (0..l).find(|y| xs.iter().zip(&ms).all(|(x, m)| (y - x).rem_euclid(*m) == 0)).unwrap_or(-1);
            let got = crt_of(&xs.iter().map(|&x| int(x)).collect::<Vec<_>>(), &ms.iter().map(|&m| int(m)).collect::<Vec<_>>());
            assert_eq!(got.unwrap(), int(want), "CRT({xs:?}, {ms:?})");
        }
        // Large coprime moduli: the least solution lies below their product.
        for _ in 0..200 {
            let ms: Vec<Integer> = (0..4).map(|_| prime(&mut s, 60)).collect();
            if (1..4).any(|i| ms[..i].contains(&ms[i])) {
                continue;
            }
            let xs: Vec<Integer> = (0..4).map(|_| &int(next(&mut s) as i64) * &int(next(&mut s) as i64)).collect();
            let x = crt_of(&xs, &ms).unwrap();
            assert!(x.sign() >= 0 && x < ms.iter().fold(int(1), |p, m| &p * m));
            assert!(xs.iter().zip(&ms).all(|(r, m)| modp(&(&x - r), m).is_zero()));
        }
    }

    #[test]
    fn modular_square_roots_square_back() {
        // Every residue modulo m < 400: a root exactly when there is one.
        for m in 2..400i64 {
            let mut square = vec![false; m as usize];
            for x in 0..m {
                square[(x * x % m) as usize] = true;
            }
            for n in 0..m {
                let r = modsqrt(&int(n), &int(m));
                assert_eq!(r.is_some(), square[n as usize], "Modsqrt({n}, {m})");
                if let Some(r) = r {
                    assert!(r.sign() >= 0 && r < int(m) && modp(&(&(&r * &r) - &int(n)), &int(m)).is_zero(), "Modsqrt({n}, {m}) = {r}");
                }
            }
        }
        // Squares modulo products of large prime powers.
        let mut s = 0x9e37_79b9_7f4a_7c15;
        for i in 0..300 {
            let mut f: Vec<(Integer, u64)> = Vec::new();
            for _ in 0..1 + i % 3 {
                let p = if next(&mut s) % 4 == 0 { int(2 + (next(&mut s) % 2) as i64) } else { prime(&mut s, 30) };
                if !f.iter().any(|(q, _)| *q == p) {
                    f.push((p, 1 + next(&mut s) % 4));
                }
            }
            f.sort();
            let m = super::super::factseq::fact_int(&f);
            let x = modp(&(&int(next(&mut s) as i64) * &int(next(&mut s) as i64)), &m);
            let n = modp(&(&x * &x), &m);
            let r = modsqrt_factored(&n, &f).unwrap_or_else(|| panic!("Modsqrt({n}, {m})"));
            assert!(modp(&(&(&r * &r) - &n), &m).is_zero(), "Modsqrt({n}, {m}) = {r}");
            assert!(is_square_mod_factored(&n, &f));
            if let Some(all) = all_sqrts_factored(&n, &f, 1 << 12) {
                assert!(all.contains(&r) && all.contains(&x) && all.iter().all(|y| modp(&(&(y * y) - &n), &m).is_zero()));
            }
        }
    }

    #[test]
    fn norm_equations_hold_and_are_complete() {
        for d in 1..=24i64 {
            for m in 0..=300i64 {
                let solvable = (0..=m.isqrt()).any(|x| (m - x * x) % d == 0 && ((m - x * x) / d).isqrt().pow(2) == (m - x * x) / d);
                let got = norm_equation(&int(d), &int(m));
                assert_eq!(got.is_some(), solvable, "NormEquation({d}, {m})");
                if let Some((x, y)) = got {
                    assert!(x.sign() >= 0 && y.sign() >= 0 && &(&x * &x) + &(&int(d) * &(&y * &y)) == int(m), "NormEquation({d}, {m}) = {x}, {y}");
                }
            }
        }
        // Large values of x^2 + d y^2.
        let mut s = 0x0123_4567_89ab_cdef;
        for _ in 0..200 {
            let (x, y, d) = (int((next(&mut s) >> 34) as i64), int((next(&mut s) >> 34) as i64), int(1 + (next(&mut s) >> 50) as i64));
            let m = &(&x * &x) + &(&d * &(&y * &y));
            let (a, b) = norm_equation(&d, &m).unwrap_or_else(|| panic!("NormEquation({d}, {m})"));
            assert_eq!(&(&a * &a) + &(&d * &(&b * &b)), m, "NormEquation({d}, {m})");
        }
    }

    #[test]
    fn linear_congruences_list_every_solution() {
        for m in 1..=40i64 {
            for a in -m..m {
                for b in -3..m {
                    let sols: Vec<i64> = (0..m).filter(|x| (a * x - b).rem_euclid(m) == 0).collect();
                    match linear_congruence(&int(a), &int(b), &int(m)) {
                        None => assert!(sols.is_empty(), "Solution({a}, {b}, {m})"),
                        Some((x0, k)) => {
                            let (x0, k) = (x0.to_i64().unwrap(), k.to_i64().unwrap());
                            assert!(0 <= x0 && x0 < k && m % k == 0, "Solution({a}, {b}, {m}) = {x0}, {k}");
                            assert_eq!(sols, (0..m).filter(|x| (x - x0) % k == 0).collect::<Vec<_>>(), "Solution({a}, {b}, {m})");
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn norm_equations_are_magmas() {
        // Magma's first solutions, where other orders of roots or common factors find another one.
        let cases = [(2, 57, 5, 4), (7, 224, 14, 2), (18, 486, 18, 3), (20, 180, 0, 3), (4, 4, 0, 1), (1, 25, 5, 0), (1, 50, 7, 1), (4, 520, 22, 3)];
        for (d, m, x, y) in cases {
            let want = Some((Integer::from_u64(x), Integer::from_u64(y)));
            assert_eq!(norm_equation(&Integer::from_u64(d), &Integer::from_u64(m)), want, "NormEquation({d}, {m})");
        }
    }
}
