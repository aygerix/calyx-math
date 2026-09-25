# Roadmap and handbook coverage

calyx follows the structure of the Magma handbook. This page tracks what is
implemented, what is deliberately different, and what is missing.

## Part I: The Magma Language

| Chapter | Status |
| --- | --- |
| Statements and expressions | Done: assignment (multiple, indexed, generator, mutation), `delete`, booleans, `eq`/`cmpeq`, coercion `!`, `where ... is`, `select`, `case` statement and expression, `for`/`while`/`repeat`, `for random`, dual iteration `i -> x`, `break x`/`continue x`, `eval`, comments and `\` continuation, `time`/`vtime`, types and extended types, `ISA`, `MakeType`, `CoveringStructure`, random seeds, `IsIntrinsic`. |
| Functions, procedures and packages | Done: `function`/`procedure` (both forms), `func<>`/`proc<>`, parameters, variadic functions, `$$`, `forward`, `local`, reference arguments (including `~A[x]` and `` ~r`f ``), closures capturing values at creation, packages with `intrinsic`, `Attach`/`Detach`/`AttachSpec`, automatic reloading of changed packages, `import`, `require`/`requirege`/`requirerange`, `Nresults`, attributes (`AddAttribute`, `declare attributes`), user-defined types (`declare type`, `New`, `Clone`, user `Print`, `Parent`, `IsCoercible`, `in`, operators), verbose flags. |
| Input and output | Mostly done: strings and their intrinsics (including `Split` and `Regexp`), `print` with print levels, `printf`/`fprintf`/`Sprintf` (widths, `%o %O %m %h`), `Sprint`, previous values `$1`..., indentation, `PrintFile`, `SetOutputFile`, `SetLogFile`, file objects (`Open`, `Gets`, `Puts`, ...), `Pipe`, `System`, `load`/`iload`, `read`/`readi`. **Missing:** binary strings, sockets, `POpen`, asynchronous I/O, `ReadObject`/`WriteObject`, `save`/`restore`. |
| Environment and options | Partly done: `-b -e -h -n -s -S -V` and `name:=value` arguments, set/get intrinsics (`SetColumns`, `SetAssertions`, `SetVerbose`, ...), `ShowIdentifiers`, `ShowValues`, `ListSignatures`, `ListCategories`, `?Name` help. **Missing:** `%p`-style history commands, most environment variables, vi mode. |
| Parallelism | Not started. |
| Magma semantics | Done (see "Differences" below). |
| Profiler | Intrinsics accepted; no profile data is collected yet. |
| Debugger | `SetDebugOnError` accepted; no debugger yet. |

## Part II: Sets, Sequences, and Mappings

| Chapter | Status |
| --- | --- |
| Introduction to aggregates | Done: universes, automatic coercion to a common overstructure, power structures, nested aggregates, multi-indexing, sequences used as universes. |
| Sets | Done: enumerated sets (with lazy arithmetic progressions), indexed sets, multisets, formal sets, all constructors, power sets, `Include`/`Exclude`/`ChangeUniverse`/..., set operators, `Subsets`, `Multisets`, `Permutations`, quantifiers `exists`/`forall`/`rep`/`random`, reductions, iteration. |
| Sequences | Done, including indexing by ranges (`s[i..j]`, `s[i..j by k]`). `Sort` gives its sorting permutation as an element of `Sym(n)`; the symmetric groups and their elements have what Part II needs (products, powers, inverses, the action `i^p`, conjugation, `Order`, `Eltseq`, `Sign`, `CycleStructure`, `Cycle`, generators, coercion from image sequences), and the rest of permutation groups comes in Part V. |
| Tuples and Cartesian products | Done. |
| Lists | Done. |
| Associative arrays | Done, including `Default` values and widening of the index universe. |
| Coproducts | Done. |
| Records | Done. |
| Mappings | Done for maps given by rules, graphs and coercions, composition, inverses and preimages. Homomorphisms given by generator images need the algebraic structures of later parts. |

## Checking against Magma

Output is checked against real Magma (V2.29-10, the version behind the
public Magma calculator). The scripts in `crates/calyx-cli/tests/compat`
have Magma's own output as their expected output, and cover print lists,
line wrapping, aggregate layout, records, error reports (source windows,
carets, call frames, `eval` errors, syntax error recovery), coercion
errors, `Sort`'s permutations, and the generic ring functions of Part III
(ring properties, element predicates and orders, ring printing and naming,
ideals of the integers, `Infinity`). Where the handbook's examples
disagree with current Magma (they were produced by many different
versions), calyx follows current Magma:
for example records print one field per line, reals print with all their
digits, and a literal such as `1/0` is rejected when it is read.

## Differences from Magma

- **Hash order.** Magma stores sets and associative arrays in hash tables.
  It prints sets of integers, rationals and residues sorted (as calyx does),
  but iterates over them, and prints sets of strings, tuples, sets and
  sequences, in its internal hash order. calyx iterates in sorted order
  (or insertion order), so loops over sets and some printed sets can list
  elements in a different order.
- **Iterator order.** In `[ e : x in X, y in Y ]` the first iterator is
  the inner loop, while in `[ e : x, y in S ]` the first variable is the
  outer one; both match Magma.
- **Extensions.** calyx also supports formal sequences `[! ... !]`, `@@`,
  `IsInjective`, `IsSurjective`, `IsBijective` and `Graph` for maps given
  by a graph, which Magma rejects.
- **Intrinsic descriptions** (`?Name`, or printing an intrinsic) use calyx's
  own documentation.
- **Random numbers** come from a different generator, so values differ from
  Magma's for the same seed. `SetSeed`/`GetSeed` behave the same way.
- **Extended reals.** Numbers mixed with `Infinity()` get the universe
  `Extended Reals` as in Magma, but keep their own types there (`Type`
  gives `RngIntElt` where Magma gives `ExtReElt`).
- **Magma's own packages.** Errors raised inside Magma's package code show
  a traceback into Magma's files (for example `ResidueClassField` of a
  non-maximal ideal); calyx reports just the error. Intrinsics Magma has
  only for other types (such as `IsMaximal`) are not declared in calyx, so
  calling them gives an undeclared-identifier error rather than "Bad
  argument types".

## Part III: Basic Rings (in progress)

The ring layer is in place: FLINT's generic rings (`gr`) provide residue
class rings, finite fields (Conway polynomials, Zech logarithms for fields
of up to 2^20 elements), univariate and multivariate polynomial rings and
the complex field. Rings are values with Magma's printing, automatic and
forced coercion, and caching (one `Integers(n)` per modulus, one default
`GF(q)`, one global `PolynomialRing(R)` per coefficient ring).

| Chapter | Status |
| --- | --- |
| Introduction to rings | Done: `Characteristic`, `#R` (`Infinity` for infinite rings), `IsFinite` and all the ring predicates (`IsField`, `IsEuclideanDomain`, `IsPID`, `IsUFD`, `HasGCD`, ..., with Magma's answers for every kind of ring), `PrimeRing`, `PrimeField`, `Centre`, ring equality and membership (with Magma's errors between unrelated rings), element predicates (`IsUnit`, `IsIdempotent`, `IsNilpotent`, `IsZeroDivisor`, `IsIrreducible`, `IsPrime`), Magma's order on residues, finite field elements and polynomials (`lt`, `Sort`), `Maximum`/`Minimum`, ideals of the integers (`ideal< >`, `quo< >`, ideal arithmetic, `ResidueClassField`), `ext< R \| >`, and naming of structures and aggregates by assignment (generators print as `F.1`, maps show `RngInt: Z`). **Pending:** `IsIrreducible`/`IsPrime` of polynomials (they need the polynomial factorisation of the polynomial chapters), ideals of polynomial rings, `Localization` and `Completion` (local rings come later). |
| Ring of integers | Done: creation (`Integers`, `IntegerRing`, `RingOfIntegers`, hexadecimal literals, `elt< >`, `sub< >`, the natural `hom< >`), coercion into Z, hexadecimal printing (`:Hex`), arithmetic and bit operations (`div`/`mod`, `Quotrem`, `ExactQuotient`, `ShiftLeft`, `Bitwise*`, `ModByPowerOf2`), predicates, `Isqrt`/`Iroot`/`IsPower`/`IsSquare`, `Ilog`, `Valuation`, digit sequences (`Intseq`/`Seqint`), gcds (`Xgcd` of sequences with small multipliers), random integers and primes, primality (proven with FLINT, `IsProbablePrime` with bases), `NextPrime`/`PreviousPrime`/`NthPrime`/`PrimesUpTo`, `Factorization` with its parameters and stored factors, the individual factoring methods (`TrialDivision`, `PollardRho`, `pMinus1`, `pPlus1`, `SQUFOF`, `ECM` with Suyama curves, `ECMOrder`, `MPQS`), `Divisors`, `CoprimeBasis`, `PartialFactorization`, `Cunningham`, factorization sequences (`RngIntEltFact`: arithmetic, divisor functions, predicates), arithmetic functions (`EulerPhi` and its inverse, `CarmichaelLambda`, `DivisorSigma`, `MoebiusMu`, `DickmanRho`), combinatorial functions, modular arithmetic (`Modexp`, `Modinv`, `Modsqrt`, `Modorder`, `PrimitiveRoot`, `Solution`, `CRT`), quadratic residue symbols and `NormEquation`. **Pending:** see "Left out of the Ring of Integers chapter" below. |
| Residue class rings, rationals, finite fields, polynomials, real and complex fields, nearfields | Not yet: the chapter-specific intrinsics come next. |

## To do

- **Confirm the pending compat scripts against Magma 2.29.** The scripts in
  `crates/calyx-cli/tests/compat/pending/` were written while the public
  calculator was offline and checked against Magma 2.22 only. Record their
  2.29 output and move them into the compat suite (see the README there):
  - `aggregate_names.m`, `aggregate_universes.m`: naming of aggregates in
    maps and by loop variables; sequences of literals without a common
    universe.
  - `integers_*.m`: the Ring of Integers chapter (the handbook examples,
    creation, arithmetic, gcds, random values, arithmetic functions,
    primes, factorization and its methods, partial factorizations,
    factorization sequences, modular arithmetic, and tables of `Modsqrt`
    roots and `NormEquation` solutions).
  - `sequence_range_index.m`: `s[i..j]` indexing and `[Any]` in the
    extended types of empty aggregates.
  - `runtime_error_continuation.m`: statements after a runtime error on
    the same line still run; after a syntax error, the statements before
    it have run.
  - `print_wrapping_per_call.m`: each `print`/`printf` wraps its output
    from column 0, whatever is already on the line.
  - `unassigned_targets.m`: assigning into or mutating an identifier that
    was never assigned.

  Where 2.22 and 2.29 differ (2.22 cannot prove primality without its
  library directory, words some errors differently, and crashes on a few
  inputs that the scripts avoid), follow 2.29.
- **Left out of the Ring of Integers chapter**, to come back to:
  - The Number Field Sieve (`NumberFieldSieve`, `NFSProcess` and its
    stages, the polynomial selection tools). It is a large, file-based
    subsystem of its own and needs the polynomial and real chapters first.
  - `AdditiveGroup(Z)`, `MultiplicativeGroup(Z)` and `ClassGroup(Z)`. They
    return abelian groups (`GrpAb`) and maps, so they wait for abelian
    groups in Part V.
  - `Cunningham(b, k, c)`, which factors b^k ± 1. Magma answers from
    tables of known factors of these numbers (the Cunningham project
    tables) that it ships with. calyx needs the same factors; without them,
    algebraic splitting of b^k ± 1 plus general factorisation gives the
    same answers but can take far longer for large k. A decoded copy of the table sits in `databases/`
    (ignored by git); how calyx will ship the factors is still to be
    decided.
  - `PrimalityCertificate`, `CheckCertificate` and `OldCertificate`. These
    need an ECPP prover that records its proof. FLINT proves primality
    by other methods and gives no certificate. A calyx certificate would be
    a valid proof, but not the same curves and points as Magma's, so only
    `CheckCertificate` could be compared directly.
- **Known differences in the Ring of Integers chapter.** Where Magma makes
  an arbitrary choice, calyx reproduces it as far as black-box testing
  against 2.22 shows; these are the cases that still differ:
  - `Modsqrt(n, 2^k)` for k >= 7 can return a different one of the square
    roots (it differs by 2^(k-1)). All other moduli tested agree.
  - `NormEquation(d, m)` returns the same first solution as Magma for 160 of
    161 tested pairs; for (2, 57) Magma gives (5, 4) and calyx (7, 2).
  - `PartialFactorization`: the cofactors (a coprime base of what is left,
    ordered by which integers they divide) always agree, and the square
    parts agree for 840 of 841 tested pairs and most longer sequences, but
    not for the handbook's four-integer example (Magma splits 15^2 as
    5^2 3^2 there) or the pair [288, 108]. The order in which Magma pairs
    up the integers is not yet understood.
  - The factoring methods are the documented algorithms, but which factor
    they find first, and the default bounds (`B2` for `pMinus1`, `pPlus1`
    and `ECM`; the random curves of `ECM` and `ECMSteps`), may differ. For
    instance `SQUFOF(360)` gives the full factorization in calyx and a
    partial one in 2.22.
  - `DickmanRho` is computed exactly (power series on each unit interval);
    2.22's values differ from the true ones by about 1e-22 on [2, 3].
  - `ECMOrder` for a singular curve reports the error without the
    traceback into Magma's package code.
  - `TrialDivision` follows the 2.29 handbook (the factors found, then the
    unfactored part); 2.22 returns the factors and a list of composites.
  - `StoreFactor` of a set stores the elements; 2.22 ignores sets.
  - `RandomPrime(0)` and `RandomPrime(1)` report an error, as 2.22 does;
    the handbook says they return 0. Check which 2.29 does.
  - Integers too long for one line inside an error message wrap at a
    space in calyx; Magma breaks them with a backslash.
  - `SetColumns(0)` stops line wrapping in calyx, but Magma also prints
    nested sequences without indentation then.

## Next

1. The rest of Part III chapter by chapter: residue class rings,
   rationals, finite fields (including towers and embeddings), univariate
   and multivariate polynomials (factorisation via FLINT), real and complex
   fields, then nearfields.
2. Generator-based constructors (`sub<>`, `quo<>`, `ext<>`, `hom<>` with
   generator images) on top of those structures.
3. Part V (groups), using GAP where it is the right tool, and Singular for
   commutative algebra.
