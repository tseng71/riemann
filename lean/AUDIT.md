# Lean audit snapshot

Date: 2026-08-12

- Upstream: `anthropics/zeta-23-lean`
- Upstream commit: `3635e74826a4c1fcece7d1cd2b6fa75e43a00510`
- Lean: `v4.33.0-rc2`
- mathlib: `51e6992efd06126df61a496bebf8f49482a4e129`
- `lake build ZetaSeven`: 8,854 jobs completed in the prepared workspace
- placeholder scan over authored `ZetaSeven` sources: no `sorry`, `admit`, or
  `axiom` token
- declaration audit: `propext`, `Classical.choice`, and `Quot.sound` only

This audit applies to the declarations enumerated in
[`../docs/FORMALIZATION_STATUS.md`](../docs/FORMALIZATION_STATUS.md). It does
not turn the externally generated Arb certificate into a Lean proof term and
does not assert the top-level manuscript proportion.
