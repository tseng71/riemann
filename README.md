# Seven-point stability refinement for zeta simple zeros

[中文说明](README.zh-CN.md)

This public repository is the review and reproducibility workspace for an
AI-assisted attempt to strengthen the known lower bound for the proportion of
simple zeros of the Riemann zeta function on the critical line.

## Status — research in progress

This repository **does not contain a proof of the Riemann hypothesis**.
It also does **not yet contain an end-to-end proof** of the candidate bound

\[
\liminf_{T\to\infty}\frac{N_0^s(T,2T)}{N(T,2T)}
\ge 0.6730254768378743181\ldots .
\]

The candidate improvement is based on a certified seven-point numerical
inequality with exact target

\[
C_* = \frac{38262312113}{10^{13}} = 0.0038262312113.
\]

The external Arb verifier has completed with no unresolved cells at two
precision settings. The finite-dimensional matrix layer, exact consecutive
window count, arbitrary principal-block spectral pinching, abstract
267-offset aggregation, conditional 267-point block bridge, exact assembly,
and an abstract defect-preserving Theorem D source inequality have been
proved in Lean without `sorry`, `admit`, or new axioms. The actual simple-zero
subtype is now enumerated by increasing ordinate as `Fin (s₁(T))`; its
normalized adjacent gaps are proved positive, and reindexing its concrete
Gram matrix is proved to preserve the full spectral defect. Every full
consecutive 267-point principal block and its 266 actual normalized gaps are
now concrete Lean objects; positivity, telescoping spans, PSD, and the
conditional local defect bridge are compiled. The concrete 267 shifted
partitions are also compiled: every full block is an actual principal fiber,
both endpoint remainders are represented explicitly, and their fiberwise
pinching bounds are aggregated. A further theorem inserts the resulting
concrete defect lower bound into the exact finite simple-zero count. The
remaining proof boundary is explicit and material: the seven-point interval
certificate must be replayed by a small verified checker, and endpoint
deletion plus a summably uniform finite Gram-to-kernel comparison error must
be proved before the asymptotic top-level specialization closes.

## Publication policy

- Claims are labelled **proved**, **externally certified**, or **open**.
- No release or paper may say “theorem” for the candidate proportion until
  the top-level proof and its dependency audit close.
- Numerical optimization is discovery only; it is not accepted as proof.
- A public draft PR contains the current paper, verifier, certificates, Lean
  extension, reproducibility instructions, provenance, and trust-base notes.

See `CLAIMS.md`, `docs/FORMALIZATION_STATUS.md`, and `docs/ROADMAP.md` for
the exact boundary and proof-closure order.

## Review focus

1. Reproduce the 128/256-bit and 160/320-bit interval runs.
2. Audit outward rounding, subdivision coverage, Hessian bounds, and basin
   containment.
3. Check the stability-enhanced rank–trace argument and block-defect bridge.
4. Check the compiled consecutive-window, principal-block pinching, concrete
   increasing-ordinate Gram reindexing, full-block specialization, concrete
   267 shifted partitions and endpoint fibers, and the finite simple-count
   assembly in `ConcreteSimpleAssembly.lean`.
5. Verify the hypotheses and concrete specialization of the new
   defect-preserving Theorem D interface, especially endpoint deletion and
   the uniform Gram-to-kernel replacement used by the local-to-global bridge.

## Attribution

The Lean extension is built against Anthropic's `zeta-23-lean` at commit
`3635e74826a4c1fcece7d1cd2b6fa75e43a00510`. Verifier provenance and inherited
licenses are recorded in the review branch. Human authorship and submission
responsibility must be settled before journal submission.

