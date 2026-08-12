# Verifier design

The verifier proves a global lower bound for a six-variable transcendental
function.  Arb handles transcendental enclosures; the main search combines
only rigorous lower bounds and exact integer cell ranges.

## Kernel cells

For grid size `G=4000`, cell `i` is the closed interval

\[
[i/G,(i+1)/G].
\]

The normalized Montgomery--Taylor kernel is evaluated through the entire
formula

\[
K(x)=\frac12\left[
\operatorname{sinc}(\pi x-1/\sqrt2)+
\operatorname{sinc}(\pi x+1/\sqrt2)\right].
\]

Arb encloses `k(x)=K(x)/K(0)` on each closed cell.  Its absolute lower
endpoint is squared, converted to binary64, and widened downward with
`math.nextafter`.  A second table encloses `w''` on cells away from the
removable singularity.  Sparse range-minimum tables answer every later query.

## Compact reduction

The target is the exact rational

\[
C_*=38262312113/10^{13}.
\]

If `sum(g_i)/3000 >= C_*`, the nonnegative kernel terms are irrelevant.
Outward integer rounding gives the pressure cutoff 45,915 cells.  On the
remaining range the one-gap contribution

\[
U(g)=g/3000+w(g)/3
\]

eliminates every cell whose rigorous lower bound reaches the target.  The
survivors form exactly three components:

```text
[3807,4780]; [7218,9373]; [10560,44945].
```

Pressure filtering leaves 435 initial products of six components.

## Box lower bounds

For each box, all 21 consecutive partial sums receive their range-minimum
lower bounds for `w`.  Coefficients and nonnegative sums are widened downward.
If this bound reaches an upward-rounded representation of the target, the box
is discarded.

When interval dependency is too weak, the verifier lower-bounds the Hessian on
the whole box using the `w''` table.  A floating-point LDL factorization is
only a heuristic filter; every success is rechecked with Arb.  Convex boxes
then receive the rigorous tangent bound

\[
F(x)\ge F(c)-\sum_i |\partial_iF(c)|r_i.
\]

## Certified minimizer basins

Two small neighborhoods, related by reversal symmetry, contain the apparent
global minimizers.  Their centers are exact rationals obtained from the
displayed terminating decimals, and their coordinate radius is exactly
`1/64`.

Across each entire basin, interval lower bounds and an Arb LDL calculation
prove

\[
\nabla^2F\succeq(3/16)I.
\]

Strong convexity therefore gives

\[
\inf F\ge F(c)-\frac{\|\nabla F(c)\|^2}{2(3/16)}.
\]

At 256-bit basin precision the rigorous lower endpoint is

```text
0.00382623121130447424827371713006270699383823035
```

for each basin, strictly above the exact target.  A search box is basin-pruned
only if every one of its closed grid cells lies inside a certified basin.

## Exhaustive subdivision

Every box not handled above is bisected along a widest coordinate.  The
program raises an exception if it reaches a terminal cell without a proof.
It also checks the binary-forest identities

```text
nodes = pruned + splits
pruned = splits + initial_boxes.
```

The canonical search has 822,433 nodes, maximum depth 39, and zero unresolved
terminal cells.

## Precision replay

The release run uses 128 bits for kernel/Hessian tables and 256 bits for basin
evaluation.  `scripts/verify_cross_precision.py` repeats the entire process at
160 and 320 bits.  Both runs have identical logical counts.  Because both use
the same Python source and Arb/FLINT implementation, agreement is a useful
precision check but not an independent verifier.

## Trust base

The finite certificate trusts:

1. CPython 3.12 and IEEE-754 binary64 semantics;
2. `python-flint==0.8.0` and its Arb/FLINT libraries;
3. the source code in this artifact;
4. the operating system and hardware executing them.

It does not trust numerical optimizer output, cached interval tables, or
committed logs.  A stronger future artifact should use an independently
implemented certificate consumer or a proof assistant.
