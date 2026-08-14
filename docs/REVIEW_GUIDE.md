# Peer-review guide

This repository separates the proposed argument into independently auditable
layers.  A reviewer should not infer the status of one layer from another.

## 1. External interval certificate

The claim is

```text
F6(g1,...,g6) >= 38262312113 / 10^13  for every gi >= 0.
```

Reproduce `verifier/scripts/verify_release.py`, then the higher-precision
replay.  Check the exact report, zero unresolved leaves, the binary-forest
identities, the interval-table hashes, outward conversions to binary64, and
the two strong-convexity basins.  The second precision is not an independent
implementation.  Also run `verifier/scripts/verify_basin_independent.py`,
which reimplements the delicate basin calculation with fresh subdivisions
and exact rational LDL arithmetic, while retaining Arb/FLINT for
transcendental intervals.

## 2. Finite-dimensional Lean layer

Build `lean/ZetaSeven` against the pinned upstream revision.  Inspect the
axiom output in `ZetaSeven/Audit.lean` and run the source scan described in
`docs/FORMALIZATION_STATUS.md`.  In particular, verify:

- the retained spectral surplus in `Stability.lean`;
- the simple-zero/remainder inertia split in `SimpleBlock.lean`;
- the off-diagonal-energy bridge in `BlockDefect.lean`;
- the consecutive-window charge count in `WindowEnergy.lean`;
- the constructed block-eigenbasis and principal-block inequality in
  `Pinching.lean`;
- the concrete simple-zero ordinate ordering, normalized positive gaps, Gram
  reindexing, and defect invariance in `OrderedSimpleZeros.lean`;
- the concrete consecutive principal blocks, gap telescoping, and specialized
  comparison interface in `ConcreteBlocks.lean`;
- the residue-fiber and 266-fold gap counts in `ShiftedPartitions.lean`;
- the conditional finite Gram-to-kernel bridge in
  `BlockEnergyDefect.lean`;
- the defect-preserving source package in `ThmDDefect.lean`;
- the epsilon-form endgame in `AsymptoticAssembly.lean`;
- the exact rational rearrangement in `Assembly.lean`.

These theorems do not prove `SevenPointClaim`.

## 3. Analytic integration

Compare Sections 2--7 of the manuscript line by line with the pinned upstream
Theorem D proof.  In particular, check the exact normalization in Corollary
3.2, uniformity of Lemma 4.1, the seven-window multiplicities, all 267 shifted
partitions, and the `O(N/L)=o(N)` accumulated block error. `ThmDDefect.lean`
retains the simple-zero Gram defect through an abstract package of the
upstream trace and tail estimates, but the concrete analytic specialization
is presently a written proof rather than a Lean theorem.

## 4. Claim language

The repository is public for adversarial review.  It is not a claim of a
Riemann-hypothesis proof.  The accurate label is **unreviewed
computer-assisted theorem**; do not call it independently verified,
peer-reviewed, formally verified end to end, or accepted until those gates in
`CLAIMS.md` have actually passed.
