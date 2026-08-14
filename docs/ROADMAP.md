# Proof-closure roadmap

The order below is dependency-driven.  A later milestone cannot upgrade the
headline claim while an earlier one is open.

## M1 — finite zero-side bridge

- split the normalized zero matrix into the simple on-line Gram block and a
  remainder of positive index at most `s₂ + p`;
- retain the spectral defect in the exact finite simple-zero count;
- prove the off-diagonal block-energy bridge;
- audit axioms and statement correspondence.

Status: implemented on the research branch; clean rebuild and review are the
merge gate.

## M2 — seven-point certificate

- specify exact dyadic/rational tables and a versioned certificate format;
- prove the transcendental enclosures used for normalized sinc and its first
  two derivatives;
- replay every subdivision/pruning node with a small trusted checker;
- compare the replayed root coverage and target with the canonical Arb run.

Status: complete at the disclosed computer-assisted-proof trust level.  The
canonical and higher-precision Arb runs agree, and a separate implementation
rechecks the two strong-convexity basins with exact rational LDL arithmetic.
A full replay in Lean or a different interval package remains a desirable
trust-base reduction, not a missing premise of the manuscript theorem.

## M3 — window and pinching layer

- formalize the sum over consecutive seven-point windows;
- prove the 267-point block inequality and the 261/262 threshold;
- prove spectral pinching for the chosen convex defect;
- formalize all 267 shifted partitions, gap multiplicities, and remainders.

Status: the consecutive-window theorem, arbitrary principal-block spectral
pinching, abstract 267 residue-fiber aggregation, exact 266-fold gap charge,
the conditional 267-point block-defect bridge, and the concrete
increasing-ordinate reindexing of the actual simple-zero Gram matrix are
compiled.  Every full consecutive 267-point block has also been concretely
constructed with its actual normalized gaps, PSD proof, telescoping span, and
specialized local bridge. All full blocks are now wired into 267 concrete
partitions of `Fin (s₁(T))`; both endpoint remainders are explicit fibers,
and concrete global pinching and finite aggregation are compiled.

## M4 — analytic Theorem D integration

- instantiate the simple-zero Gram block in the concrete zero-side data;
- retain the defect through the tail perturbation and trace/Frobenius bounds;
- prove uniform overlap replacement on bounded 267-point spans;
- account for endpoint deletion and every asymptotic error;
- close the top-level epsilon-form proportion theorem.

Status: complete in the mathematical manuscript.  Corollary 3.2 and Lemma
4.1 prove the concrete source specialization, central endpoint deletion,
uniform finite-Gram comparison, and `o(N)` accumulation over all 267 shifts.
The abstract finite-dimensional and asymptotic assembly layers compile in
Lean; translating the new analytic estimates and Arb certificate into one
end-to-end Lean theorem remains open.

## M5 — release and review

- reproduce all checks from an immutable revision on a second machine;
- obtain independent number-theory and computer-assisted-proof reviews;
- resolve authorship and submission responsibility;
- archive a tagged release with hashes and, ideally, a DOI.

M1--M4 support the present label: **unreviewed computer-assisted theorem**.
M5 is the gate for claims of independent verification, peer-reviewed
acceptance, priority, or a permanent archival release.  None of these
milestones would constitute a proof of the Riemann hypothesis.
