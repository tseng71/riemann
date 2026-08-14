# Audit of the seven-point interval certificate

Date: 2026-08-14

## Claim checked

For every `g_1,...,g_6 >= 0`, the release verifier proves

\[
 F_6(g)=\frac1{3000}\sum_{i=1}^6g_i+
 \sum_{r=1}^6\frac2{7-r}\sum_{i=1}^{7-r}
 w(g_i+\cdots+g_{i+r-1})
 \ge \frac{38262312113}{10^{13}},
\]

where `w=k^2` and

\[
 k(x)=\frac{\operatorname{sinc}(\pi x-1/\sqrt2)+
                 \operatorname{sinc}(\pi x+1/\sqrt2)}
                {2\sqrt2\sin(1/\sqrt2)}.
\]

Here `sinc(z)=sin(z)/z`.  The audit below checks the mathematical direction
of every pruning rule and records a clean local replay.

## 1. Coverage of the noncompact domain

Let `G=4000`, `C=38262312113/10^13`, and

\[
 q=\lceil 3000GC\rceil=45915.
\]

If `sum g_i >= q/G`, then the linear term alone is at least `C`.  Therefore
only coordinates in cells

\[
 I_j=[j/G,(j+1)/G],\qquad 0\le j<q,
\]

need to be considered.

For each coordinate, the summand

\[
 U(g_i)=g_i/3000+w(g_i)/3
\]

is part of `F_6` and every omitted term is nonnegative.  Hence a cell is
discarded only when a rigorous lower bound for `U` already exceeds an upper
binary64 enclosure of `C`.  The cells not discarded are exactly the three
contiguous components

```text
[3807,4780]  [7218,9373]  [10560,44945].
```

Their sixfold products cover all remaining coordinate choices.  Products
whose component lower endpoints already have total index at least `q` are
again proved by the linear term.  This leaves exactly 435 initial boxes.

Thus the initial search boxes, the one-coordinate exclusions, and the
linear pressure region cover all of `[0,infinity)^6`; there is no numerical
compactness assumption.

## 2. Rigorous cell lower bounds

`closed_cell(j,G)` is the exact Arb ball `I_j`.  The code evaluates the
entire sinc expression for `k` on that ball.  If the resulting interval does
not contain zero, its `abs_lower()` is a lower bound for `|k|`; otherwise the
lower bound is zero.  Squaring with outward-rounded nonnegative arithmetic
therefore gives a rigorous lower bound for `w` on the whole closed cell.

Every conversion to binary64 is widened by `nextafter(...,-infinity)`.
Products and sums of nonnegative lower bounds are widened once more in the
same direction.  Rational coefficients have separate downward and upward
binary64 enclosures; the upward enclosure is used when multiplying a
negative lower bound for `w''`.  Consequently all stored scalar values are
on the safe side of the exact real quantity.

For a box whose `i`th coordinate spans cells `[a_i,b_i]`, a sum of `r`
consecutive coordinates lies in every cell from

\[
 \sum a_i\quad\hbox{through}\quad \sum b_i+r-1.
\]

The range-minimum query uses precisely these inclusive endpoints.  If a
partial-sum range extends beyond the table, the code substitutes zero, which
is still a valid lower bound because `w>=0`.

## 3. Convex tangent pruning

For a term `c w(g_s+...+g_{s+r-1})`, the Hessian is

\[
 c w''(g_s+\cdots+g_{s+r-1})uu^{\mathsf T},
\]

where `u` is the indicator of the relevant consecutive coordinates.  A
cellwise lower bound `ell` for `w''` therefore yields the Loewner lower
bound `c ell uu^T`, even when `ell<0`.

The release code first performs a binary64 LDL calculation only as a speed
filter.  Every successful filter is then rechecked after converting each
binary64 lower coefficient to its exact dyadic rational and performing an
Arb LDL calculation.  A box is declared convex only when every interval
pivot is strictly positive.

For a convex box with exact rational center `c` and coordinate radii `r_i`,

\[
 F_6(x)\ge F_6(c)+\nabla F_6(c)\mathbin{\cdot}(x-c)
 \ge F_6(c)-\sum_i |\partial_iF_6(c)|r_i.
\]

Both the value and gradient at `c` are evaluated with Arb.  Subtracting Arb
upper bounds for the absolute gradient contributions makes this a rigorous
box lower bound.

## 4. Strong-convexity basins

Two boxes, related by reversal, surround the numerical minimizers.  Their
center coordinates are exact terminating rationals and every radius is
exactly `1/64`.  The release verifier proves on each whole basin that

\[
 \nabla^2F_6\succeq(3/16)I.
\]

It then uses the standard strong-convexity inequality

\[
 \inf F_6\ge F_6(c)-\frac{\|\nabla F_6(c)\|^2}{2(3/16)}.
\]

At 256 bits the rigorous lower endpoint is

```text
0.00382623121130447424827371713006270699383823035
```

which exceeds the exact target by more than `4.47e-15`.

The separate script `verifier/scripts/verify_basin_independent.py` does not
import the release verifier.  It reimplements the sinc quotient derivatives,
subdivides every scalar sum interval into 2,048 fresh rational pieces, and
forms the shifted Hessian over exact `fmpq` arithmetic.  Exact no-pivot LDL
proves positive definiteness for both basins.  It independently obtains the
lower endpoint

```text
0.003826231211304474248273717130062706993838230354884912386
```

and ends with `independent_basin_certificate=pass`.  This is an independent
control path, but it deliberately retains Arb/FLINT as the transcendental
interval trust base.

A search node is basin-pruned only if all six of its closed cell ranges are
contained in one of the certified rational basins.

## 5. Exhaustive subdivision

Every box not discharged by pressure, a direct interval lower bound, a
convex tangent, or a strong-convexity basin is bisected along a widest cell
coordinate.  Integer cell ranges are split into disjoint children whose
union is the parent.  If all six ranges are single cells and no proof rule
applies, the program raises an exception; it never treats such a leaf as
verified.

The local replay at commit `b8dcb42c88f920fca2c609b1c88a5cc133d88b2a`
used CPython 3.12 and the exact locked wheel

```text
python_flint-0.8.0-...manylinux...whl
sha256=af60dbed2b0e3bedef2875ff3a2b32afec12f7152595d65fcd674713ac09a208
```

All ten unit tests passed.  The final canonical 128/256-bit replay completed
in 105.867 seconds and matched every deterministic release field:

```text
initial_boxes=435
nodes=822433
pruned=411434
splits=410999
maximum_depth=39
interval_pruned=285258
pressure_pruned=2872
tangent_pruned=122329
strong_convexity_pruned=975
unresolved_terminal_cells=0
release_certificate=match
```

The identities

\[
 822433=411434+410999,
 \qquad 411434=410999+435
\]

are also checked at runtime.  They are consistent with a complete forest of
435 binary roots and no silently dropped node.

A second local replay with table precision raised from 128 to 160 bits and
basin precision from 256 to 320 bits completed in 121.030 seconds.  It
produced the same domain components, forest counts, pruning counts, maximum
depth, and basin lower endpoint, and ended with
`cross_precision_certificate=match`.  Its independently regenerated
second-derivative table had the published SHA-256
`fd634c87441380105aad52f069f735108d0dabcd7d5d0a993b6abc52ee12b055`.

## 6. Audit conclusion

The domain cover, interval directions, Hessian lower bounds, convex tangent
rule, basin containment, and binary subdivision are mathematically sound.
Together with the successful locked-environment replay, they constitute a
computer-assisted proof of the displayed seven-point inequality, relative
to the explicitly stated software/hardware trust base.  A proof-assistant
replay could reduce that trust base, but is not logically required for the
mathematical proposition.
