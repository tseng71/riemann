# ZetaSeven Lean extension

This directory contains only the new `ZetaSeven` extension. It is not a
standalone copy of the much larger upstream development. The CI workflow
clones `anthropics/zeta-23-lean` at commit
`3635e74826a4c1fcece7d1cd2b6fa75e43a00510`, overlays these files, and then
builds the extension against mathlib commit
`51e6992efd06126df61a496bebf8f49482a4e129` with Lean `v4.33.0-rc2`.

## What is proved

The compiled declarations cover the finite-dimensional rank--trace surplus,
the simple-zero Gram/remainder split, the off-diagonal spectral-energy
bridge, exact consecutive-window combinatorics, arbitrary principal-block
spectral pinching, abstract 267-offset aggregation, the conditional
267-point block bridge, concrete increasing-ordinate coordinates and
defect-preserving reindexing for the actual simple-zero Gram matrix, the
concrete consecutive 267-point principal blocks with telescoping normalized
gaps, the finite tail seam, an abstract defect-preserving Theorem D source
inequality, epsilon removal, and exact rational assembly. See
[`../docs/FORMALIZATION_STATUS.md`](../docs/FORMALIZATION_STATUS.md) for the
declaration-level ledger.

## What is not proved

`SevenPointClaim` is intentionally a definition of a proposition, not a
theorem. The Arb interval forest is not replayed in Lean.  The compiled
increasing-ordinate index has not yet been restricted to the retained central
sublist or connected to concrete 267 partitions, endpoint remainders,
endpoint deletion, and a uniform Gram-to-kernel error in a top-level theorem. Therefore this
package does not prove the candidate proportion and does not prove the
Riemann hypothesis.

## Rebuild

The exact commands used by CI are in `.github/workflows/lean.yml`. After the
files have been overlaid on the pinned upstream checkout, run:

```bash
ulimit -n 65536 2>/dev/null || true
lake build ZetaSeven
lake env lean ZetaSeven/Audit.lean
rg -n '(^|[^[:alnum:]_])(sorry|admit|axiom)([^[:alnum:]_]|$)' \
  ZetaSeven ZetaSeven.lean
```

The last command must return no matches. The current axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.
