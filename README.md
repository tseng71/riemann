# Seven-point stability refinement for zeta simple zeros

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
precision settings. Several finite-dimensional matrix and assembly lemmas
have been proved in Lean without `sorry`, `admit`, or new axioms. The remaining
proof boundary is explicit and material: the seven-point interval certificate
must be replayed by a small verified checker, and the retained spectral defect
must be carried through the full analytic Theorem D chain, including window
sums, pinching, endpoints, and all asymptotic errors.

## Publication policy

- Claims are labelled **proved**, **externally certified**, or **open**.
- No release or paper may say “theorem” for the candidate proportion until
  the top-level proof and its dependency audit close.
- Numerical optimization is discovery only; it is not accepted as proof.
- A public draft PR contains the current paper, verifier, certificates, Lean
  extension, reproducibility instructions, provenance, and trust-base notes.

See `CLAIMS.md` and `docs/FORMALIZATION_STATUS.md` for the exact boundary.

## Review focus

1. Reproduce the 128/256-bit and 160/320-bit interval runs.
2. Audit outward rounding, subdivision coverage, Hessian bounds, and basin
   containment.
3. Check the stability-enhanced rank–trace argument and block-defect bridge.
4. Check consecutive seven-window multiplicities and the 267 shifted
   partitions.
5. Verify that the spectral defect survives every analytic approximation and
   endpoint deletion in the imported Theorem D framework.

## Attribution

The Lean extension is built against Anthropic's `zeta-23-lean` at commit
`3635e74826a4c1fcece7d1cd2b6fa75e43a00510`. Verifier provenance and inherited
licenses are recorded in the review branch. Human authorship and submission
responsibility must be settled before journal submission.
