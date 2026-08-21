# Higher Even Derivatives: Mathematical and Lean Roadmap

This note collects the conclusions reached while studying how the smoothing
problem should extend beyond the fourth and sixth derivatives.  It separates
three things which are easy to conflate:

1. the sharp variational theorem, which Lean already proves at every even
   order;
2. an implicit forward construction by finitely many hyperelliptic period
   equations;
3. a theta-function formula for the solution of those equations.

Throughout, “derivative order `2m`” refers to the corresponding `2m`-fold
forward-difference norm in the discrete smoothing problem.  Let `n` be the
support radius and put

```text
N = n + m,                 g = floor((m - 1) / 2).
```

Here `N` is the degree of the normalized alternant and `g` is the smallest
possible genus of its squarefree Pell--Abel curve.

## What is already unconditional and Lean-verified

For every `m ≥ 1` and every support radius `n`, the current development:

- constructs an admissible kernel minimizing the `2m`-fold difference norm;
- proves the sharp lower bound and characterizes equality;
- proves that the attaining kernel is unique;
- extracts from its normalized alternant `Z` polynomials `Q` and `D` with

  ```text
  Z² - D Q² = 1;
  ```

- proves that `D` is monic, squarefree, has degree `2g+2`, and is negative on
  the open interval `(-1,1)`;
- proves the exact endpoint multiplicities and the differential identity

  ```text
  Z' = N (x-1)^g Q;
  ```

- constructs a strictly increasing real phase `φ` on `[-1,1]` and proves

  ```text
  Z(x) = ε cos(N φ(x)),       N φ(1) = (n+1)π,
  ```

  where `ε` is the endpoint orientation;
- expresses the sharp constant through the endpoint coefficient of `D`:

  ```text
  C(2m,n) = 2^m (-1)^(m+1) m² δ_m / (n+m)²,
  ```

  where `δ_m = D'(1)` for odd `m` and `δ_m = D(1)` for even `m`.

These results are in
[`JoseSmoothest/EvenOrder.lean`](JoseSmoothest/EvenOrder.lean),
[`JoseSmoothest/EvenOrder/PellExtraction.lean`](JoseSmoothest/EvenOrder/PellExtraction.lean),
[`JoseSmoothest/EvenOrder/EndpointPhase.lean`](JoseSmoothest/EvenOrder/EndpointPhase.lean),
and
[`JoseSmoothest/EvenOrder/DirectClassification.lean`](JoseSmoothest/EvenOrder/DirectClassification.lean).

Thus there is no remaining existence, optimality, or uniqueness gap at
higher even order.  The remaining question is how to construct or evaluate
`D` *without first obtaining it from the variational minimizer*.

## The genus staircase

The endpoint contact consumes critical multiplicity and forces the following
minimal-genus hierarchy:

| difference order | `m` | genus `g` | expected function theory |
|---:|---:|---:|---|
| 2 | 1 | 0 | rational/Chebyshev |
| 4 | 2 | 0 | rational/Chebyshev |
| 6 | 3 | 1 | elliptic/Zolotarev |
| 8 | 4 | 1 | elliptic |
| 10 | 5 | 2 | hyperelliptic |
| 12 | 6 | 2 | hyperelliptic |

Each increase of `m` by two raises the minimal genus by one.  This explains
why the sixth-order calculation is qualitatively harder than the
fourth-order one, and why a Jacobi-elliptic library alone cannot settle all
higher orders.

## The best all-order target: an implicit period construction

The most useful next theorem is not a general theta formula.  It is a
finite-dimensional period characterization of the unique polynomial `D`.

Start with a marked real hyperelliptic curve

```text
y² = D(x)
```

of degree `2g+2`.  On it consider the distinguished endpoint differential

```text
η_D = (x-1)^g dx / y.
```

Its residues at the two points at infinity are fixed by monicity.  The desired
curve is characterized by:

- integral/torsion conditions on the periods of `N η_D`;
- the prescribed real branch topology and endpoint contact;
- the phase-length condition giving exactly `n+1` half-turns on `[-1,1]`;
- a discrete cycle-label vector determined by the real critical graph.

The period equations should be formulated first for all closed loops.  A
later finite-basis theorem can replace these by a square system in the branch
parameters.  This separation avoids making a full singular-homology library
a prerequisite of the first useful result.

There are two valid notions of existence:

- **Existence from the verified minimizer.**  Extract its `D` and prove that
  it solves the period equations.  This gives a rigorous nonempty and unique
  system, suitable for certified numerical computation.
- **Independent analytic existence.**  Prove directly that the real period
  map has a solution, for example by properness and degree, flat-surface
  gluing, or a global theorem about the relevant Pell--Abel stratum.  This is
  mathematically stronger but is a separate research problem.

The first notion is already enough for a polished forward *characterization*.
It is not circular for computation: once uniqueness is known, a numerical
solver can recover the curve from the finite equations without solving the
original minimax problem.

## The identification theorem that saves most of the work

The decisive reusable theorem should say that any forward candidate with the
right Pell, endpoint, sign, and winding data is automatically the canonical
optimizer.

Suppose a proposed construction supplies `D`, `P`, and `Q` such that

```text
P² - DQ² = 1,              P' = N(x-1)^gQ,
```

with `P(1)=1`, exact order-`m` contact at `1`, `D<0` on `(-1,1)`, and the
required `n+1` half-turns.  Then:

1. the Pell equation or the real phase gives `|P|≤1` on `[-1,1]`;
2. exact contact lets us divide `1-P` by `(1-x)^m`;
3. after endpoint normalization, the quotient is nonnegative and equals one
   at `x=1`;
4. the phase produces the complete alternating zero--peak node set;
5. the existing minimax uniqueness theorem identifies that quotient with
   `canonicalEvenWeightedExtremalData.S`;
6. consequently `P` is the canonical normalized alternant, and monic
   squarefree Pell-factor uniqueness identifies `D` with the extracted
   canonical weight.

This argument means the future analytic library only has to construct a
candidate and verify its geometric data.  It does not have to repeat the
variational proof separately in every genus.

## Parity and real branch topology

The implemented algebra already proves that `-1` is a simple root of `D` and
that the multiplicity at `1` is `m mod 2`.  The forward construction will
need a sharper global description of the remaining real roots.

A promising target, which is **not yet a Lean theorem and must be proved
before becoming part of the public API**, is:

- for `m=2g+1`, write `D=(x²-1)R`, with the residual degree-`2g` factor in
  the appropriate positive real cell;
- for `m=2g+2`, write `D=(x+1)(x-ρ)R` for a marked `ρ>1`, with the residual
  degree-`2g` factor in the corresponding positive cell.

This predicts respectively `2g` and `2g+1` real moduli before the period and
phase equations are imposed.  It also explains the parity of the endpoint
differential:

- at odd contact order, its zero is concentrated at the branch point over
  `x=1`;
- at even contact order, the zeros split between the two points above
  `x=1`.

The precise positivity region and cycle labels should be derived from the
critical graph, not guessed from low-degree pictures.  Until that proof is
complete, the period-data structure should carry the marking and labels
explicitly.

## Low-genus milestones

The implementation should advance through the following regression gates.

### Genus zero: orders two and four

For `m=1`, the extracted quadratic should reduce to `D=X²-1`, giving

```text
C(2,n) = 4/(n+1)².
```

For `m=2`, the generic development should be identified with the existing
weighted-Chebyshev module.  With

```text
θ = π/(2(n+2)),
```

the expected quadratic normal form is

```text
D = (X+1)(X-(1+2 tan² θ)),
```

which recovers the already verified fourth-order constant.  These bridges
require polynomial uniqueness and elementary algebra, not integration.

### Genus one: sixth derivative

For any supplied `CubicZolotarevData (n+3)`, the identification theorem should
prove

```text
endpointQuotient = canonical minimizer,
Z = canonical normalized alternant,
D = (X²-1)H,
D'(1) = 2r²,
C(6,n) = 144r²/(n+3)².
```

This bridge is algebraic and should be kept downstream of the unconditional
`EvenOrder` development.  It does **not** construct the elliptic data.  The
remaining analytic theorem must produce `CubicZolotarevData`, prove existence
of the distinguished modulus `k_N`, and identify its abstract `r` with the
paper's ratio

```text
(1-cn(2a))/dn(2a).
```

The current repository intentionally makes no such identification.

### Genus one: eighth derivative

The eighth-order case tests the other endpoint parity without yet increasing
the genus.  First expose the unconditional quartic Pell weight and its cubic
core, endpoint value, sign, and phase integral.  Only after that normal form
is stable should an explicit Jacobi parametrization be attempted.

### Genus two and beyond

Orders ten and twelve are the first tests of the genuinely hyperelliptic
library.  Work should not start here until the sixth- and eighth-order cases
validate both parity conventions, the infinity residues, the cycle marking,
and polynomial descent.

Useful diagonal sanity checks at `n=0`, to prove when the low-genus bridge is
implemented, are:

| `m` | expected `D` | sharp constant |
|---:|---|---:|
| 1 | `X²-1` | 4 |
| 2 | `(X-1)²-4` | 16 |
| 3 | `(X²-1)(X²-4X+7)` | 64 |
| 4 | `(X-1)⁴-16` | 256 |

These are regression targets, not claims currently exported by Lean.

## Three possible stopping points

| target | mathematical output | status and scale |
|---|---|---|
| Supplied-curve criterion | periods iff a marked `D` supports the required Pell solution | high confidence; smallest reusable analytic layer |
| Finite implicit construction | square period system, uniqueness, certified numerical recovery of `D` | substantial but bounded; roughly 6–12 person-months for a polished cut-basis library |
| General theta formula | period matrices, Abel maps, theta, prime forms, divisor recovery, polynomial descent | long-term program; roughly 12–30 person-months and some research risk |

A specialized genus-one construction for the sixth derivative is much
smaller than the all-genus program: approximately 6–10 focused weeks for a
pragmatic result, or several person-months if developed as a reusable
elliptic-function library.  These are planning estimates, not commitments.

The all-genus theta layer is optional.  Even after it is formalized, the
answer is generally “explicit” only in terms of a period matrix and a solution
of transcendental moduli equations.  The finite period characterization may
therefore be the most natural final theorem for higher derivative orders.

## Recommended implementation order

1. Prove the genus-zero formulas and the algebraic sixth-order identification
   bridge.
2. Formalize the unconditional genus-one Zolotarev construction for order
   six; use minimizer uniqueness as the final identification step.
3. State a small marked `ForwardEndpointPeriodData` API and prove the
   supplied-curve, all-loop period criterion.
4. Specialize it to the extracted canonical `D`, establishing nonemptiness
   and uniqueness of the period system at every genus.
5. Reduce all-loop quantization to a finite marked cut basis and add certified
   numerical evaluation.
6. Test even endpoint parity at order eight.
7. Begin genus two.
8. Add period matrices, theta functions, and prime forms only if a genuinely
   explicit evaluation theorem requires them.

The existing detailed statement-first module plans live in
[`blueprint/JoseSmoothest/SpecialFunctions.md`](blueprint/JoseSmoothest/SpecialFunctions.md).
That file remains authoritative for the proposed Lean declaration surfaces;
this roadmap records the mathematical strategy and project boundary.
