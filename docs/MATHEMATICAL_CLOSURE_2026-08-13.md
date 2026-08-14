# Mathematical closure audit: the analytic bridge

Date: 2026-08-13  
Scope: mathematics first; no Lean theorem is used as a substitute for any
analytic estimate in this note.

## 1. Conclusion of this audit

The endpoint value `lambda = 1` is admissible.  Claude's Theorem 5.8 and
Remark 6.1 explicitly retain it, with relative error
`O(log log T / log T)`.  Thus no `lambda < 1`, `T -> infinity`,
`lambda -> 1` diagonal argument is required for the proposed refinement.

The new spectral defect can be retained with coefficient one in the finite
zero-side inequality.  After deleting narrow endpoint strips, the finite
simple-zero Gram entries converge uniformly, on every fixed normalized
separation range, to the normalized Montgomery--Taylor kernel.  For the
fixed block size 267, the accumulated replacement error is `o(N)`.

This closes the previously informal endpoint/Gram-to-kernel part of the
argument at the level of a conventional written proof.  It does not by
itself independently validate Claude's prime-side Theorem 5.8, and it does
not replace the separate computer-assisted proof of the six-variable local
inequality.

## 2. Notation and the exact finite inequality

Put

\[
  \ell=\log(T/2\pi),\qquad L=\ell,\qquad h=2\pi/L,
  \qquad N=N(T,2T).
\]

Use Claude's optimized window from Theorem D, with a fixed-width smooth
endpoint ramp.  Let

\[
  a_L={1\over L}\int_{\mathbb R}\phi_L(u)^2\,du,
  \qquad \tau_k=T+kh,
  \qquad d=\lfloor T/h\rfloor.
\]

For a simple critical-line zero of ordinate `gamma`, define the normalized
finite Gabor column

\[
 v_\gamma={1\over \sqrt{a_LL^2}}
     \bigl(\widehat\phi_L(\gamma-\tau_k)\bigr)_{0\le k<d}.
\]

The full-grid identity gives

\[
 \sum_{k\in\mathbb Z}|\widehat\phi_L(\gamma-\tau_k)|^2=a_LL^2,
\]

so every finite column has norm at most one.

Let `Abar` be Claude's normalized zero-side matrix over
`I'=(T-T^(1/2),2T+T^(1/2)]`, let `P1=VV*` be the contribution of the simple
critical-line zeros in `I'`, and let `M=V*V`.  If `s1` is their number,
`s2` is the number of distinct multiple critical-line zeros, and `p` is the
number of off-line functional-equation pairs, then the remainder
`Q'=Abar-P1` has at most `s2+p` positive eigenvalues.  The stability lemma in
the manuscript therefore gives

\[
 \|\overline A\|_F^2
 \ge 4\operatorname{tr}\overline A-3s_1-4s_2-4p+\mathcal D(M).
\]

Since `N(I') >= s1+2s2+2p`, this rearranges, with no asymptotic step, to

\[
 s_1\ge 4\operatorname{tr}\overline A-
       \|\overline A\|_F^2-2N(I')+\mathcal D(M).       \tag{2.1}
\]

This is exactly Claude's Proposition 4.4(ii), with the additional
nonnegative term `D(M)` retained.  Nothing in the later comparison of
`Abar` with the prime-side matrix acts on this term.

## 3. Central deletion costs `o(N)`

Delete the simple zeros of `(T,2T]` lying in either physical strip

\[
 (T,T+hL^2]\quad\hbox{or}\quad(2T-hL^2,2T].             \tag{3.1}
\]

The width of each strip is `hL^2=2*pi*L`.  The standard local count used in
Claude's Proposition 4.2,

\[
 N(t+1)-N(t)\ll\log(t+3),
\]

shows that the total number deleted is

\[
 O(L\log T)=O(L^2)=o(N),                               \tag{3.2}
\]

because the Riemann--von Mangoldt formula gives `N asymp T L`.

Let `M_c` be the principal Gram submatrix belonging to the retained central
simple zeros.  Pinching `M` into `M_c` and its complement and using convexity
of `X -> tr Psi(X)` yields

\[
 \mathcal D(M)\ge \mathcal D(M_c).                     \tag{3.3}
\]

The zeros of `I'` outside `(T,2T]` number
`O(T^(1/2)L)=o(N)`.  Applying (2.1), then Claude's Proposition 4.2 and
Theorem 5.8 at `lambda=1`, gives

\[
 N_0^s(T,2T)
 \ge H_{MT}N+\mathcal D(M_c)-o(N),                     \tag{3.4}
\]

where

\[
 H_{MT}={3\over2}-{1\over\sqrt2}\cot {1\over\sqrt2}.
\]

For clarity, the source-side main term in (3.4) is

\[
 4\operatorname{tr}\overline G-
 \|\overline G\|_F^2-2N
 =\left(2-{1\over c_1^*}\right)N-o(N)=H_{MT}N-o(N).
\]

The trace-norm comparison error from `Abar=Gbar-Ebar` is `o(N)` by Claude's
Proposition 4.2 and the estimate `||Gbar||_F=O(N^(1/2))`.  The defect in
(3.4) is not perturbed or absorbed into this error.

## 4. Uniform finite-Gram to sharp-kernel comparison

Define

\[
 q(t)=\cos(\sqrt2t)\,1_{[-1/2,1/2]}(t),\qquad
 K(x)=\int_{-1/2}^{1/2}q(t)e^{-2\pi ixt}\,dt,
\]

and `k(x)=K(x)/K(0)`.  Here

\[
 K(0)=\sqrt2\sin(1/\sqrt2)>0.
\]

If `q_L(t)=phi_L(Lt)^2`, the fixed-width endpoint ramp implies

\[
 \|q_L-q\|_1\le {C_0\over L},\qquad
 |a_L-K(0)|\le {C_0\over L},                            \tag{4.1}
\]

with an absolute constant depending only on the fixed ramp.  Consequently,
for all real `x` (bounded `x` is all that is needed),

\[
 \left|
 {\int q_L(t)e^{-2\pi ixt}\,dt\over a_L}-k(x)
 \right|\le {C_1\over L}.                              \tag{4.2}
\]

It remains to replace the full `k in Z` sum by `0 <= k < d`.  Claude's
integration-by-parts bound for the optimized fixed-ramp window gives a
constant `C_2`, independent of `L`, such that

\[
 |\widehat\phi_L(r)|\le {C_2\over r^2}\quad(r\ne0).     \tag{4.3}
\]

For a retained ordinate, its distance from every omitted grid point is at
least

\[
 D_L=h(L^2-2)\ge \pi L
\]

for all sufficiently large `L`.  Therefore, on either side of the finite
grid,

\[
 \sum_{j\ge0}(D_L+jh)^{-4}
 \le D_L^{-4}+{1\over3hD_L^3}=O(L^{-2}).                \tag{4.4}
\]

Cauchy--Schwarz, (4.3), and (4.4) show that the omitted product tail is
`O(L^(-2))`.  After division by `a_L L^2`, its contribution to a normalized
Gram entry is `O(L^(-4))`.  Combining this with (4.2), uniformly for retained
ordinates, gives

\[
 \langle v_\gamma,v_{\gamma'}\rangle
 =k\left({L(\gamma-\gamma')\over2\pi}\right)+O(L^{-1}). \tag{4.5}
\]

The implied constant is independent of the particular zeros.  In
particular it is uniform for every pair in every fixed 267-point block whose
normalized span is below 500.

Since both normalized Gram entries and `k` have modulus at most one, (4.5)
also gives

\[
 \left|\,|\langle v_\gamma,v_{\gamma'}\rangle|^2-
 k\left({L(\gamma-\gamma')\over2\pi}\right)^2\right|
 \le {C_3\over L}.                                     \tag{4.6}
\]

## 5. Summability over all 267-point blocks

Let `m=267` and

\[
 A_0=(m-6)C_*=261C_*=0.9986463461493<1.
\]

For a consecutive `m`-point block `B`, if its normalized span is at least
`500 A0`, then nonnegativity of the defect proves

\[
 \mathcal D(G_B)+{\operatorname{span}(B)\over500}\ge A_0.
\]

Otherwise the span is below 500, so (4.6) applies to all
`m(m-1)/2` pairs.  The seven-point inequality and the block-defect lemma then
give, with one error `epsilon_L=O(1/L)` independent of `B`,

\[
 \mathcal D(G_B)+{\operatorname{span}(B)\over500}
 \ge A_0-\epsilon_L.                                   \tag{5.1}
\]

Across all 267 shifted partitions, every consecutive 267-point window is
used once.  Their number is at most the number `S_c` of retained simple
zeros, hence at most `N`.  Thus the total error in (5.1) is

\[
 O(N\epsilon_L)=O(N/L)=o(N).                            \tag{5.2}
\]

Each adjacent normalized gap occurs in at most `m-1=266` window spans, and

\[
 x_{S_c}-x_1\le {LT\over2\pi}=N+o(N).                  \tag{5.3}
\]

Averaging the 267 pinching inequalities therefore gives

\[
 \mathcal D(M_c)\ge {261C_*\over267}S
       -{266\over 500\cdot267}N-o(N).                  \tag{5.4}
\]

Substitution of (5.4) into (3.4) and rearrangement yields

\[
 \liminf_{T\to\infty}{N_0^s(T,2T)\over N(T,2T)}
 \ge {267H_{MT}-266/500\over267-261C_*}.               \tag{5.5}
\]

With `C*=38262312113/10^13`, the right side is

\[
 0.6730254768378743181159739993\ldots .
\]

## 6. Remaining proof boundary

The written analytic bridge is now explicit.  Before the headline can be
promoted without qualification, the following still deserve independent
checking:

1. replay or independently reimplement the Arb certificate for the exact
   six-variable inequality;
2. audit the correspondence between the symbols in (2.1)--(3.4) and the
   exact normalization in Claude's source, especially the fixed-ramp
   optimized window;
3. obtain specialist review of the new stability lemma and the use of trace
   convexity under pinching;
4. independently assess the still-new Claude Theorem D on which the
   prime-side asymptotic is based.

These are review/trust tasks, not missing asymptotic terms in the
local-to-global passage proved above.
