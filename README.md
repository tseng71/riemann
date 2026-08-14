# Seven-point stability refinement for zeta simple zeros

[中文说明](README.zh-CN.md)

This public repository is the review and reproducibility workspace for an
AI-assisted, computer-assisted refinement of the lower bound for the
proportion of simple zeros of the Riemann zeta function on the critical line.

## Status — unreviewed computer-assisted theorem

This repository **does not contain a proof of the Riemann hypothesis**.
The manuscript proves, relative to the explicitly stated Arb/FLINT trust base
and Claude's cited Theorem D,

\[
\liminf_{T\to\infty}\frac{N_0^s(T,2T)}{N(T,2T)}
\ge 0.6730254768378743181\ldots .
\]

Claude's cited Montgomery--Taylor value is
`67.2500703679412%`; the absolute increase is approximately
`0.0524773158463` percentage points.

The improvement is based on a certified seven-point inequality
inequality with exact target

\[
C_* = \frac{38262312113}{10^{13}} = 0.0038262312113.
\]

The Arb verifier exhausts the noncompact six-gap domain after rigorous
pressure reduction: both precision settings visit 822,433 nodes with zero
unresolved terminal cells. A separate implementation rechecks the two
delicate strong-convexity basins using fresh subdivisions and exact rational
LDL arithmetic, while retaining Arb/FLINT for transcendental intervals.

The paper now supplies the previously missing mathematical bridge: central
endpoint deletion costs `o(N)`, every retained finite Gram entry differs
uniformly from the limiting Montgomery--Taylor kernel by `O(1/log T)`, and
the error over every full block in all 267 shifted partitions is `o(N)`.
Together with the stability inequality, block pinching, certified local
inequality, and Claude's trace asymptotics, this yields the displayed bound.

The Lean companion checks much of the finite-dimensional algebra and exact
arithmetic without `sorry`, `admit`, or new axioms. It is deliberately
partial: the Arb forest and the analytic endpoint/kernel estimates have not
been translated into one end-to-end Lean theorem. That is a formalization
boundary, not an omitted premise in the written mathematical proof.

## Publication policy

- Claims distinguish **proved in the manuscript**, **computer certified**,
  **Lean proved**, and **open formalization/review**.
- The proportion is described as an **unreviewed computer-assisted theorem**,
  not as an independently accepted result.
- Numerical optimization is discovery only; it is not accepted as proof.
- A public draft PR contains the current paper, verifier, certificates, Lean
  extension, reproducibility instructions, provenance, and trust-base notes.

See `paper/riemann.pdf`, `CLAIMS.md`,
`docs/INTERVAL_CERTIFICATE_AUDIT_2026-08-14.md`, and
`docs/FORMALIZATION_STATUS.md` for the proof and its trust boundary.

## Review focus

1. Reproduce the 128/256-bit and 160/320-bit interval runs.
2. Audit outward rounding, subdivision coverage, Hessian bounds, and basin
   containment.
3. Check the stability-enhanced rank–trace argument and block-defect bridge.
4. Check the compiled consecutive-window, principal-block pinching, concrete
   increasing-ordinate Gram reindexing, full-block specialization, concrete
   267 shifted partitions and endpoint fibers, and the finite simple-count
   assembly in `ConcreteSimpleAssembly.lean`.
5. Verify the normalization against Claude's Theorem D, the endpoint
   deletion, the uniform Gram-to-kernel estimate, and summation of all 267
   shifted-block errors in Sections 2--7 of the manuscript.

## Attribution

The Lean extension is built against Anthropic's `zeta-23-lean` at commit
`3635e74826a4c1fcece7d1cd2b6fa75e43a00510`. Verifier provenance and inherited
licenses are recorded in the review branch. Human authorship and submission
responsibility must be settled before journal submission.
