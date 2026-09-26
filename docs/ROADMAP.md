# Roadmap and handbook coverage

calyx follows the structure of the Magma handbook. This page summarises
what is implemented and what is deliberately different. Open work (bugs,
missing features, known differences from Magma) is tracked as
[GitHub issues](https://github.com/aygerix/calyx-math/issues); see "Open
work" at the end.

## Part I: The Magma Language

| Chapter | Status |
| --- | --- |
| Statements and expressions | Done: assignment (multiple, indexed, generator, mutation), `delete`, booleans, `eq`/`cmpeq`, coercion `!`, `where ... is`, `select`, `case` statement and expression, `for`/`while`/`repeat`, `for random`, dual iteration `i -> x`, `break x`/`continue x`, `eval`, comments and `\` continuation, `time`/`vtime`, types and extended types, `ISA`, `MakeType`, `CoveringStructure`, random seeds, `IsIntrinsic`. |
| Functions, procedures and packages | Done: `function`/`procedure` (both forms), `func<>`/`proc<>`, parameters, variadic functions, `$$`, `forward`, `local`, reference arguments (including `~A[x]` and `` ~r`f ``), closures capturing values at creation, packages with `intrinsic`, `Attach`/`Detach`/`AttachSpec`, automatic reloading of changed packages, `import`, `require`/`requirege`/`requirerange`, `Nresults`, attributes (`AddAttribute`, `declare attributes`), user-defined types (`declare type`, `New`, `Clone`, user `Print`, `Parent`, `IsCoercible`, `in`, operators), verbose flags. |
| Input and output | Mostly done: strings and their intrinsics (including `Split` and `Regexp`), `print` with print levels, `printf`/`fprintf`/`Sprintf` (widths, `%o %O %m %h`), `Sprint`, previous values `$1`..., indentation, `PrintFile`, `SetOutputFile`, `SetLogFile`, file objects (`Open`, `Gets`, `Puts`, ...), `Pipe`, `System`, `load`/`iload`, `read`/`readi`. **Missing:** binary strings, sockets, `POpen`, asynchronous I/O, `ReadObject`/`WriteObject`, `save`/`restore` ([#27](https://github.com/aygerix/calyx-math/issues/27)). |
| Environment and options | Partly done: `-b -e -h -n -s -S -V` and `name:=value` arguments, set/get intrinsics (`SetColumns`, `SetAssertions`, `SetVerbose`, ...), `ShowIdentifiers`, `ShowValues`, `ListSignatures`, `ListCategories`, `?Name` help. **Missing:** `%p`-style history commands, most environment variables, vi mode ([#28](https://github.com/aygerix/calyx-math/issues/28)). |
| Parallelism | Not started ([#29](https://github.com/aygerix/calyx-math/issues/29)). |
| Magma semantics | Done (see "Differences" below). |
| Profiler | Intrinsics accepted; no profile data is collected yet ([#30](https://github.com/aygerix/calyx-math/issues/30)). |
| Debugger | `SetDebugOnError` accepted; no debugger yet ([#31](https://github.com/aygerix/calyx-math/issues/31)). |

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
| Mappings | Done for maps given by rules, graphs and coercions, composition, inverses and preimages. Homomorphisms given by generator images need the algebraic structures of later parts ([#33](https://github.com/aygerix/calyx-math/issues/33)). |

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
  elements in a different order. For example `Subsets({1..8}, 1)` prints
  as `{3}, {6}, {1}, ...` in Magma. `PartialFactorization` does reproduce
  Magma's iteration order of `Subsets({1..n}, 1)`, which it depends on
  ([#32](https://github.com/aygerix/calyx-math/issues/32)).
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
the complex field; real and complex numbers are computed with MPFR. Rings
are values with Magma's printing, automatic and forced coercion, and
caching (one `Integers(n)` per modulus, one default `GF(q)`, one global
`PolynomialRing(R)` per coefficient ring).

| Chapter | Status |
| --- | --- |
| Introduction to rings | Done: `Characteristic`, `#R` (`Infinity` for infinite rings), `IsFinite` and all the ring predicates (`IsField`, `IsEuclideanDomain`, `IsPID`, `IsUFD`, `HasGCD`, ..., with Magma's answers for every kind of ring), `PrimeRing`, `PrimeField`, `Centre`, ring equality and membership (with Magma's errors between unrelated rings), element predicates (`IsUnit`, `IsIdempotent`, `IsNilpotent`, `IsZeroDivisor`, `IsIrreducible`, `IsPrime`), Magma's order on residues, finite field elements and polynomials (`lt`, `Sort`), `Maximum`/`Minimum`, ideals of the integers (`ideal< >`, `quo< >`, ideal arithmetic, `ResidueClassField`), `ext< R \| >`, and naming of structures and aggregates by assignment (generators print as `F.1`, maps show `RngInt: Z`). **Pending:** `IsIrreducible`/`IsPrime` of polynomials ([#34](https://github.com/aygerix/calyx-math/issues/34)), ideals of polynomial rings ([#35](https://github.com/aygerix/calyx-math/issues/35)), `Localization` and `Completion` ([#36](https://github.com/aygerix/calyx-math/issues/36)). |
| Ring of integers | Done, pending validation against 2.29 ([#24](https://github.com/aygerix/calyx-math/issues/24)): creation (`Integers`, `IntegerRing`, `RingOfIntegers`, hexadecimal literals, `elt< >`, `sub< >`, the natural `hom< >`), coercion into Z, hexadecimal printing (`:Hex`), arithmetic and bit operations (`div`/`mod`, `Quotrem`, `ExactQuotient`, `ShiftLeft`, `Bitwise*`, `ModByPowerOf2`), predicates, `Isqrt`/`Iroot`/`IsPower`/`IsSquare`, `Ilog`, `Valuation`, digit sequences (`Intseq`/`Seqint`), gcds (`Xgcd` of sequences with small multipliers), random integers and primes, primality (proven with FLINT, `IsProbablePrime` with bases), `NextPrime`/`PreviousPrime`/`NthPrime`/`PrimesUpTo`, `Factorization` as a pipeline of methods that honours its limit parameters, with stored factors, the individual factoring methods (`TrialDivision`, `PollardRho`, `pMinus1`, `pPlus1`, `SQUFOF`, `ECM` with Suyama curves, `ECMOrder`, `MPQS` as a self-initialising quadratic sieve), `Divisors`, `CoprimeBasis`, `PartialFactorization`, `Cunningham`, factorization sequences (`RngIntEltFact`: arithmetic, divisor functions, predicates), arithmetic functions (`EulerPhi` and its inverse, `CarmichaelLambda`, `DivisorSigma`, `MoebiusMu`, `DickmanRho`), combinatorial functions, modular arithmetic (`Modexp`, `Modinv`, `Modsqrt` with Magma's choice of root, `Modorder`, `PrimitiveRoot`, `Solution`, `CRT`), quadratic residue symbols, `NormEquation`, and `AdditiveGroup`, `MultiplicativeGroup` and `ClassGroup` of Z. **Pending:** see the [`area: integers` issues](https://github.com/aygerix/calyx-math/issues?q=is%3Aopen+label%3A%22area%3A+integers%22). |
| Residue class rings | Done, pending validation against 2.29 ([#24](https://github.com/aygerix/calyx-math/issues/24)): creation (`Integers(m)`, `IntegerRing(m)` and `ResidueClassRing(m)` of an integer or a factorization, `quo< >`), `Modulus`/`FactoredModulus`, square roots (`IsSquare`, `Sqrt`, `AllSquareRoots`, with Magma's choice of root), `Solution`, gcds and lcms of elements, `Normalize`, ideals (`ideal< >`, `sub< >`, sums, products, intersections, membership, `Generator`), the unit group (`UnitGroup`/`MultiplicativeGroup` with Magma's generators, discrete logarithms by Pohlig–Hellman with baby-step giant-step or Pollard's rho, `IsPrimitive`, `PrimitiveElement`, `Order`), `AdditiveGroup`, the natural `hom< >` between residue class rings, and the abelian groups these return (`GrpAb`: elements and their arithmetic, `Invariants`, `Order`, `Exponent`, `IsCyclic`, `Generators`, maps and preimages). **Pending:** Dirichlet characters ([#48](https://github.com/aygerix/calyx-math/issues/48)). |
| Rational field | Done, pending validation against 2.29 ([#24](https://github.com/aygerix/calyx-math/issues/24)): Q as a number field (`MaximalOrder`, the bases, `MinimalField`, `UnitGroup`, `ClassGroup`, `AutomorphismGroup`, `Decomposition`, the invariants, `DefiningPolynomial`, `Signature`), creation (`RootOfUnity`, `Random`, `Q.1`, `Q![n, d]`, `elt< >`, the natural `hom< >`), and elements: `Height`, `Qround`, regular and Hirzebruch-Jung continued fractions, `RationalReconstruction` of residues and prime field elements, `Valuation` at primes and prime ideals, `Eltseq`, `MinimalPolynomial`. Also Z as a number field order (`Decomposition`, `RamificationIndex`, `TwoElementNormal`, `ChineseRemainderTheorem` and `Valuation` at ideals). **Pending:** `Algebra`, `VectorSpace` and matrix `RationalReconstruction` ([#53](https://github.com/aygerix/calyx-math/issues/53)). |
| Finite fields | In progress ([#39](https://github.com/aygerix/calyx-math/issues/39)). |
| Nearfields | Not yet ([#43](https://github.com/aygerix/calyx-math/issues/43)). |
| Univariate polynomial rings | Done, pending validation against 2.29 ([#24](https://github.com/aygerix/calyx-math/issues/24)): creation and print options, structure operations, coefficients and terms, roots (`Roots`, `HasRoot` and `Roots(f : Max := m)` with Magma's choice of roots), derivatives, evaluation and interpolation, division, `Modexp` and `CRT`, gcds, content, resultants and discriminants, integer polynomial norms and `DedekindTest`, polynomials over finite fields (`PrimePolynomials` in Magma's order, `JacobiSymbol`), factorization (irreducible, squarefree, distinct- and equal-degree, Hensel lifting, `IsIrreducible`, `IsPrime`), ideals and quotient rings (`ideal< >`, `quo< >`), the special families (Chebyshev, Legendre, Laguerre, Hermite, Bernoulli, Gegenbauer, Dickson, Swinnerton-Dyer) and Magma-level printing. **Pending:** roots over the reals and complexes, `Decomposition`, `SmallRoots`, the matrix functions, rational functions and the rest of [#57](https://github.com/aygerix/calyx-math/issues/57). |
| Multivariate polynomial rings | In progress ([#41](https://github.com/aygerix/calyx-math/issues/41)). |
| Real and complex fields | In progress ([#42](https://github.com/aygerix/calyx-math/issues/42)): creation, structure, element operations, printing and the transcendental functions (handbook sections 254 to 258) are done; the elliptic and modular functions are next, and real literals with a precision wait on [#54](https://github.com/aygerix/calyx-math/issues/54). |

## Open work

Everything still to do is a GitHub issue, labelled by area (`area:
integers`, `area: rings`, ...), kind (`bug`, `missing`,
`known-difference`, `perf`, `testing`) and priority (`P1` to `P3`), with
one milestone per handbook Part:

- [Open issues](https://github.com/aygerix/calyx-math/issues)
- [Known differences from Magma](https://github.com/aygerix/calyx-math/issues?q=is%3Aopen+label%3Aknown-difference)
- [Waiting on Magma 2.29](https://github.com/aygerix/calyx-math/issues?q=is%3Aopen+label%3Aneeds-2.29),
  including the pending compat scripts ([#24](https://github.com/aygerix/calyx-math/issues/24))

After the rest of Part III come the generator-based constructors ([#33](https://github.com/aygerix/calyx-math/issues/33))
and Part V ([#44](https://github.com/aygerix/calyx-math/issues/44)).
