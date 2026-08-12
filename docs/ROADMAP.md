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

## M2 — proof-carrying seven-point certificate

- specify exact dyadic/rational tables and a versioned certificate format;
- prove the transcendental enclosures used for normalized sinc and its first
  two derivatives;
- replay every subdivision/pruning node with a small trusted checker;
- compare the replayed root coverage and target with the canonical Arb run.

Status: Arb evidence complete; Lean/independent replay open.

## M3 — window and pinching layer

- formalize the sum over consecutive seven-point windows;
- prove the 267-point block inequality and the 261/262 threshold;
- prove spectral pinching for the chosen convex defect;
- formalize all 267 shifted partitions, gap multiplicities, and remainders.

Status: the consecutive-window theorem, arbitrary principal-block spectral
pinching, abstract 267 residue-fiber aggregation, exact 266-fold gap charge,
and the conditional 267-point block-defect bridge are compiled.  Concrete
reindexing of the ordered central-zero Gram matrix into the 267 residue
partitions and endpoint remainders remains open.

## M4 — analytic Theorem D integration

- instantiate the simple-zero Gram block in the concrete zero-side data;
- retain the defect through the tail perturbation and trace/Frobenius bounds;
- prove uniform overlap replacement on bounded 267-point spans;
- account for endpoint deletion and every asymptotic error;
- close the top-level epsilon-form proportion theorem.

Status: concrete finite zero-side entry point and tail seam implemented in
Lean. The abstract defect-preserving Theorem-D source inequality and its
`o(N)` error package are also implemented. The finite local-to-global
combinatorial and spectral core is now available; central-window replacement,
uniform Gram-to-kernel error control, concrete partition/remainder wiring,
and the top-level specialization remain open.

## M5 — release and review

- reproduce all checks from an immutable revision on a second machine;
- obtain independent number-theory and computer-assisted-proof reviews;
- resolve authorship and submission responsibility;
- archive a tagged release with hashes and, ideally, a DOI.

Only after M1–M5 pass may the candidate proportion be labelled proved.  None
of these milestones would constitute a proof of the Riemann hypothesis.
