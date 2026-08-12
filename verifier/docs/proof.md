# Proof map with exact constants

This note records the deduction in the accompanying manuscript.  It takes the
analytic trace, tail, inertia, and Gabor-overlap framework stated in Claude's
Theorem D and its proof as imported input.  The new finite proposition is
certified by the code in this artifact.

## 1. Imported baseline

Write

\[
N=N(T,2T),\qquad S=N_0^s(T,2T),
\]

and set

\[
H_{\rm MT}=\frac32-\frac1{\sqrt2}\cot\frac1{\sqrt2}
=0.6725007036794116457343797908\ldots .
\]

For the optimized window, the normalized overlap kernel is

\[
k(x)=\frac{K(x)}{K(0)},\qquad
K(x)=\int_{-1/2}^{1/2}\cos(\sqrt2t)\cos(2\pi xt)\,dt,
\quad K(0)=\sqrt2\sin(1/\sqrt2).
\]

After deleting `o(N)` endpoint zeros, bounded normalized separations satisfy

\[
\langle v_\gamma,v_{\gamma'}\rangle
=k(x_\gamma-x_{\gamma'})+o(1)
\]

uniformly.

## 2. Stability defect

Define

\[
\Psi(t)=\begin{cases}(t-1)^2,&0\le t\le2,\\2t-3,&t\ge2,
\end{cases}
\qquad \mathcal D(M)=\operatorname{tr}\Psi(M).
\]

If the columns of `V` have norm at most one, `P=VV*`, `M=V*V`, and the
Hermitian matrix `Q` has at most `b` positive eigenvalues, then

\[
\|P+Q\|_F^2\ge
4\operatorname{tr}(P+Q)-3r-4b+\mathcal D(M).
\]

The scalar step is

\[
\min_{n\ge0}\big((p-n)^2+4n\big)=2p-1+\Psi(p).
\]

Inserted into the imported zero-side decomposition, this retains the defect:

\[
S\ge H_{\rm MT}N+\mathcal D(M^\circ)-o(N), \tag{2.1}
\]

where `M°` is the Gram matrix of the retained central simple zeros.

## 3. Certified seven-point inequality

Put `w=k^2`.  For six nonnegative gaps define

\[
\mathcal F_6(g_1,\ldots,g_6)=
\frac1{3000}\sum_{i=1}^6g_i+
\sum_{r=1}^6\frac2{7-r}\sum_{i=1}^{7-r}
w(g_i+\cdots+g_{i+r-1}).
\]

The interval verifier proves

\[
\mathcal F_6(g_1,\ldots,g_6)\ge C_*,\qquad
C_*:=\frac{38262312113}{10^{13}}=0.0038262312113. \tag{3.1}
\]

This claim is global on `[0,infinity)^6`; numerical optimization is not part
of the proof.

## 4. Consecutive-block energy

For ordered points `y_1<...<y_m`, set

\[
E_m=2\sum_{1\le i<j\le m}w(y_j-y_i).
\]

Summing (3.1) over all consecutive seven-point windows gives

\[
E_m+\frac{y_m-y_1}{500}\ge C_*(m-6). \tag{4.1}
\]

For a positive semidefinite Gram block `G`,

\[
\operatorname{tr}\Psi(G)\ge
\min\left\{1,2\sum_{i<j}|G_{ij}|^2\right\}. \tag{4.2}
\]

Choose `m=267`.  Then

\[
A_0=C_*(267-6)=0.9986463461493<1, \tag{4.3}
\]

whereas `C_*(268-6)=1.0024725773606>1`.  Uniform kernel convergence on
bounded spans and (4.1)--(4.2) yield, for every consecutive 267-point block,

\[
\mathcal D(G_B)+\frac{\operatorname{span}(B)}{500}
\ge A_0-o(1). \tag{4.4}
\]

## 5. Shifted pinching

Average (4.4) over the 267 offsets of consecutive block partitions.  Spectral
pinching bounds the sum of block defects by the global defect.  Each interior
gap appears in at most 266 block spans, and the total normalized ordinate
length is `N+o(N)`.  Hence

\[
\mathcal D(M^\circ)\ge
\frac{261C_*}{267}S-\frac{266}{133500}N-o(N). \tag{5.1}
\]

Substitution of (5.1) into (2.1) gives

\[
\left(1-\frac{261C_*}{267}\right)S
\ge\left(H_{\rm MT}-\frac{266}{133500}\right)N-o(N).
\]

Therefore

\[
\liminf_{T\to\infty}\frac{S}{N}
\ge
\frac{267H_{\rm MT}-266/500}{267-261C_*}. \tag{5.2}
\]

The exact reduced linear-fractional expression is

\[
\frac{2670000000000000H_{\rm MT}-5320000000000}
{2660013536538507}
=0.67302547683787431811597399932145\ldots .
\]

## 6. Scope

Equation (3.1) is the only computer-assisted mathematical input added by this
artifact.  The stability lemma, block deduction, and arithmetic are proved in
the manuscript.  The analytic trace estimates, error bounds, endpoint
truncation, and optimized test family remain dependencies of the cited
Claude/Anthropic paper and its Lean companion.  Thus this package is not a
proof of the Riemann hypothesis and is not yet an independently reviewed
unconditional theorem.

## 7. Formal-proof boundary

The pinned `ZetaSeven` Lean extension proves the finite-dimensional
rank--trace surplus, the simple-zero Gram/remainder inertia split, the finite
tail seam, the scalar and matrix spectral-energy bridges (including the exact
`2 * sum_{i<j}` off-diagonal form), epsilon-removal and rational assembly, and
an abstract defect-preserving Theorem D source inequality under the pinned
trace/tail hypotheses, with no `sorry`, `admit`, or new axiom.  It deliberately
leaves `SevenPointClaim` as a proposition rather than a theorem.  It also does
not yet prove the concrete local-to-global specialization: central-window
replacement, 267 shifted partitions, pinching, endpoint deletion, and the
uniform Gram-to-kernel error passage remain open.

Thus the current evidence has two complementary but non-identical parts:
Arb certifies (3.1) externally, while Lean certifies the surrounding algebra.
The top-level candidate proportion is not yet a closed Lean theorem.
