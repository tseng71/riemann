# Provenance and attribution

## Artifact chain

1. Claude's paper *More Than Two Thirds of the Zeros of the Riemann Zeta
   Function Lie on the Critical Line* (August 10, 2026) supplies the analytic
   framework and Montgomery--Taylor constant used here.  Anthropic also
   published a Lean 4 companion artifact for that paper.
2. The public repository `ainta/zeta-simple-zeros`, commit
   `040c5e899e658aed7b56a2a87f501798fe10761d`, introduced the
   stability-defect approach and a verifier for the local target `0.0038`.
3. The clean-room repository `learademacher/ai-refines-ai-zeta-bound`, commit
   `bd4a7d36988b23220034527881f4457f2f689e86`, certified the stronger target
   `0.00382` and packaged a manuscript and audit trail.
4. The present snapshot raises the certified local target to the exact
   rational `38262312113/10^13`.  It adds two rational strong-convexity basins,
   higher-precision replay, hard binary-forest invariants, and revised paper
   and audit documentation.

## Authorship disclosure

The present manuscript and software modifications are AI-assisted.  The
anonymous author line is a submission placeholder, not a claim that a human
author has approved every argument.  A prospective submitter must replace it
with the responsible authors' names and obtain their explicit approval.

The upstream package metadata credits `ainta`; that credit is retained.
No independent human peer review is represented by this artifact.

## Licenses

The inherited verifier code is distributed under the MIT License in
`LICENSE`.  Links and quotations from external papers remain under their
respective owners' terms.  Anthropic's Lean repository is a cited dependency,
not copied into this package.

## Primary links

- Anthropic paper: <https://www-cdn.anthropic.com/564f962e60643842f5fcb4a17c9dbc8f608f1c37.pdf>
- Anthropic Lean artifact: <https://github.com/anthropics/zeta-23-lean>
- First public verifier: <https://github.com/ainta/zeta-simple-zeros>
- Clean-room verifier: <https://github.com/learademacher/ai-refines-ai-zeta-bound>
