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
implementation.

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
- the residue-fiber and 266-fold gap counts in `ShiftedPartitions.lean`;
- the conditional finite Gram-to-kernel bridge in
  `BlockEnergyDefect.lean`;
- the defect-preserving source package in `ThmDDefect.lean`;
- the epsilon-form endgame in `AsymptoticAssembly.lean`;
- the exact rational rearrangement in `Assembly.lean`.

These theorems do not prove `SevenPointClaim`.

## 3. Analytic integration

Compare the manuscript's interface line by line with the pinned upstream
Theorem D proof. `ThmDDefect.lean` now retains the simple-zero Gram defect
through an abstract package of the upstream trace and tail estimates and
proves that the remaining source error is `o(N)`. The decisive open task is
the concrete local-to-global lower bound for that defect: certificate replay,
reindexing the ordered central-zero Gram matrix into the already formalized
principal-block/residue-fiber interfaces, endpoint remainders and deletion,
uniform overlap replacement, and a concrete top-level specialization. Until
this path is formalized or independently checked, the candidate proportion
is not an established theorem.

## 4. Claim language

The repository is public for adversarial review.  It is not a claim of a
Riemann-hypothesis proof, and the numerical proportion must remain labelled
“candidate” or “open end-to-end” until every release gate in `CLAIMS.md`
passes.
