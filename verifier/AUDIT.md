# Technical audit and review status

## Verdict at this release

The finite claim

\[
\mathcal F_6(g_1,\ldots,g_6)\ge 0.0038262312113
\quad(g_i\ge0)
\]

has been verified by exhaustive interval computation at two precision
settings.  Lean checks now cover the stability inequality, seven-window
combinatorics, arbitrary principal-block pinching, abstract 267-offset
counting, and exact final arithmetic; hand checks found no error in the
remaining kernel normalization and analytic wiring.  The corresponding
global proportion is

\[
0.6730254768378743181159739993\ldots .
\]

The correct review label is nevertheless **candidate computer-assisted
refinement**.  The new argument has not been independently peer reviewed; the
second run changes precision but not the implementation or interval library;
and the analytic foundation is imported from Theorem D of Claude's 2026
paper rather than rebuilt here.

## Claim ledger

| Claim | Evidence in this artifact | Current status |
|---|---|---|
| Stability-enhanced rank--trace inequality | Manuscript plus `ZetaSeven.Stability` | Compiled Lean proof; independent review pending |
| Off-diagonal Gram energy to spectral defect | Manuscript plus `ZetaSeven.BlockDefect` | Compiled Lean proof; independent review pending |
| Simple-zero Gram block and remainder inertia | `ZetaSeven.SimpleBlock` | Compiled Lean proof, including concrete zeta-zero instantiation |
| Defect-preserving finite tail seam | `ZetaSeven.SeamDefect` | Compiled Lean proof; independent review pending |
| Abstract defect-preserving Theorem D source inequality | `ZetaSeven.ThmDDefect` | Compiled Lean proof under the pinned trace/tail hypotheses; concrete specialization remains open |
| Epsilon-removal and rational final assembly | `ZetaSeven.AsymptoticAssembly`, `ZetaSeven.Assembly` | Compiled Lean proof; independent review pending |
| Montgomery--Taylor overlap kernel | Derivation from the full-grid identity; normalization tests | Hand checked; depends on cited tail estimates |
| Local seven-point inequality | Arb interval search, exact expected report, hard terminal-cell failure | Reproduced at 128/256 and 160/320 bits |
| Seven-window block inequality | `ZetaSeven.WindowEnergy` | Compiled Lean proof conditional only on the displayed `SevenPointClaim` |
| Principal-block spectral pinching | `ZetaSeven.Pinching` | Compiled Lean proof for arbitrary finite sigma-type partitions |
| Concrete ordered simple-zero Gram coordinates | `ZetaSeven.OrderedSimpleZeros` | Compiled Lean proof of increasing-ordinate enumeration, positive normalized gaps, exact Gram reindexing, and defect invariance |
| Shifted 267-block arithmetic | `ZetaSeven.ShiftedPartitions` | Compiled Lean proof at the residue-fiber interface; retained-sublist partition and remainder wiring remain open |
| 267-point block defect | `ZetaSeven.BlockEnergyDefect` | Compiled Lean proof conditional on `SevenPointClaim` and an explicit finite Gram-to-kernel error bound |
| Final constant | Exact rational reduction, Arb evaluation, and `ZetaSeven.Assembly` | Compiled Lean arithmetic proof; independent review pending |
| Underlying analytic trace/tail estimates | Claude, Theorem D and cited propositions | Imported; not independently rebuilt here |

## Matrix inequality

For columns of norm at most one, let `P=VV*`, `M=V*V`, and let the Hermitian
matrix `Q` have at most `b` positive eigenvalues.  With

\[
\Psi(t)=\begin{cases}(t-1)^2,&0\le t\le2,\\2t-3,&t\ge2,\end{cases}
\]

the manuscript proves

\[
\|P+Q\|_F^2\ge
4\operatorname{tr}(P+Q)-3r-4b+\operatorname{tr}\Psi(M).
\]

The critical scalar identity is

\[
\min_{n\ge0}\{(p-n)^2+4n\}=2p-1+\Psi(p).
\]

Von Neumann's trace inequality is used in the direction that pairs the
decreasing eigenvalues of `P` and `Q_-`.  The final replacement
`-2 tr(P)-r >= -3r` follows from the column-norm hypothesis.

## Kernel and local functional

The normalized overlap kernel is

\[
k(x)=\frac{K(x)}{K(0)},\qquad
K(x)=\int_{-1/2}^{1/2}\cos(\sqrt2t)\cos(2\pi xt)\,dt,
\]

with `K(0)=sqrt(2) sin(1/sqrt(2))`.  The code evaluates the equivalent entire
sinc formula, avoiding removable singularities.  For `w=k^2`,

\[
\mathcal F_6(g)=\frac1{3000}\sum_{i=1}^6g_i+
\sum_{r=1}^6\frac2{7-r}\sum_{i=1}^{7-r}
w(g_i+\cdots+g_{i+r-1}).
\]

The canonical search uses grid 4000 and pressure cutoff 45,915 cells.  The
surviving one-gap components are

```text
[3807,4780]; [7218,9373]; [10560,44945]
```

and generate 435 initial six-dimensional component products after pressure
filtering.

## Strong-convexity basins

The only boxes that remain too close to the numerical minimizers for ordinary
interval or tangent pruning are handled by a separate proof.  On the
coordinatewise radius-`1/64` neighborhoods of the rational center

```text
(1.04608035577, 1.98913202062, 1.98641493611,
 1.04160329372, 1.97702352234, 1.04500209462)
```

and its reversal, interval lower bounds for `w''` give
`Hessian(F6) >= (3/16) I`.  At 256-bit precision the strong-convexity
estimate

\[
F(c)-\frac{\|\nabla F(c)\|^2}{2(3/16)}
\]

has rigorous lower endpoint

```text
0.00382623121130447424827371713006270699383823035
```

which exceeds the exact target by more than `4.47e-15`.

## Exhaustive-search invariants

The canonical run records:

```text
nodes=822433
pruned=411434
splits=410999
maximum_depth=39
unresolved_terminal_cells=0
interval_pruned=285258
pressure_pruned=2872
tangent_pruned=122329
strong_convexity_pruned=975
```

The identities `nodes = pruned + splits` and
`pruned = splits + initial_boxes` are checked in the program.  Every pruning
rule is a rigorous lower bound; numerical optimization is used only to locate
the rational basin centers and is not trusted by the proof.

## Block and final arithmetic

Summing the local inequality over consecutive seven-point windows gives

\[
E_m+\frac{y_m-y_1}{500}\ge C_*(m-6),\qquad
C_*=\frac{38262312113}{10^{13}}.
\]

For `m=267`, `C_*(m-6)=0.9986463461493<1`; at `m=268` the value is
`1.0024725773606`, so the block-defect cap activates and the bound decreases.
The exact final expression is

\[
\frac{2670000000000000H_{\rm MT}-5320000000000}
{2660013536538507}.
\]

## Open review items

1. An expert should verify the concrete specialization of the abstract
   defect-preserving Theorem D interface, including the local-to-global
   seven-point passage and every uniform error term.
2. A second implementation, preferably in a proof assistant or a different
   interval package, should independently certify the local inequality.
3. The manuscript's priority and comparison claims should be checked against
   the rapidly changing 2026 literature before publication.
4. Authorship, acknowledgments, and a permanent repository/DOI must be supplied
   before journal submission.
5. The Arb subdivision forest must be replayed by a small independent or Lean
   checker before the local inequality can be called formally verified.
6. Selecting the retained central sublist from the compiled increasing-
   ordinate Gram coordinates, wiring its 267 residue partitions and endpoint
   remainders, central-window replacement, and the uniform Gram-to-kernel
   limit remain to be closed in Lean.  The concrete full-list ordering and
   defect-preserving reindexing, finite window, spectral pinching, abstract
   shifted arithmetic, and source-side defect retention are already compiled.
