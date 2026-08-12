# ZetaSeven Lean formalization status

Date: 2026-08-12

This branch is a **partial formalization of the seven-point stability
refinement**, not a proof of the Riemann hypothesis and not yet a closed Lean
proof of the proposed `67.3025476...%` simple-zero proportion.  The purpose of
this file is to make the exact verification boundary reviewable.

## Pinned base

- Upstream source: `anthropics/zeta-23-lean`
- Upstream commit: `3635e74826a4c1fcece7d1cd2b6fa75e43a00510`
- Lean: `leanprover/lean4:v4.33.0-rc2`
- mathlib: `51e6992efd06126df61a496bebf8f49482a4e129`

The new library root is `ZetaSeven`.  The upstream `Zeta23` source is retained
so the extension can be rebuilt against exactly the audited base.

## Closed, compiled theorems

| Lean declaration | Mathematical role |
| --- | --- |
| `ZetaSeven.Stability.rank_trace_spectral_gc` | Retains the full spectral `g_c` surplus before the Schur/diagonal relaxation in Claude's multiplicity-aware rank--trace proof. |
| `ZetaSeven.Stability.psi_eq_gc_add_one` | Proves the exact identity `Psi(x) = g_2(x) + 1`. |
| `ZetaSeven.Stability.min_one_sum_sq_sub_one_le_sum_psi` | Proves the scalar spectral energy bridge `min(1, sum (lambda_i-1)^2) <= sum Psi(lambda_i)`. |
| `ZetaSeven.Stability.sum_sq_sub_one_eigenvalues_eq_frob_sub_card` | Converts squared spectral deviation into Frobenius excess for a PSD matrix of normalized trace. |
| `ZetaSeven.Stability.min_one_frob_sub_card_le_spectralDefect` | Matrix form of the local energy bridge. |
| `ZetaSeven.Stability.gram_defect_rank_trace` | Proves the strengthened Gram-matrix inequality `||P+Q||_F^2 >= 4 tr(P+Q)-3r-4b+D(M)`. |
| `ZetaSeven.Assembly.finite_zero_counting` | Checks the finite zero-count bookkeeping after the strengthened matrix inequality. |
| `ZetaSeven.Assembly.Cstar_*` | Checks `C_*`, the `261/262` threshold, both exact block values, and denominator positivity by rational normalization. |
| `ZetaSeven.Assembly.assemble_stability` | Checks the global linear rearrangement, with both error terms explicit. |
| `ZetaSeven.Assembly.assemble_stability_div` | Checks the positive-denominator quotient form. |
| `ZetaSeven.Assembly.sigma_exact_form` | Checks the exact linear-fractional expression with denominator `2660013536538507`. |

All declarations above compile without `sorry`, `admit`, or a new `axiom`.

## Exact open boundary

`ZetaSeven.SevenPointSpec` defines the normalized sinc kernel, the complete
six-gap functional `F6`, and the proposition

```text
SevenPointClaim : for all nonnegative g1,...,g6,
  Cstar <= F6 g1 g2 g3 g4 g5 g6.
```

The module deliberately does **not** declare that proposition as a theorem.
The present Python/Arb run is strong external evidence, but an Arb log is not a
Lean proof term.

The remaining end-to-end work is:

1. Prove rational enclosures for `sqrt 2`, `pi`, `sin`, `cos`, and `sinc`
   using Taylor remainders in Lean.
2. Emit proof-carrying dyadic bounds for the 45,923 kernel cells and the
   second-derivative cells used by the verifier.
3. Replay the 822,433-node subdivision forest with a small verified checker.
   The preferred route is chunked kernel reduction; if `native_decide` is used
   instead, its larger trust base must be disclosed explicitly.
4. Formalize the consecutive-window sum, pinching, 267 shifted partitions,
   endpoint errors, and the modified Theorem D endgame that retains the defect
   rather than discarding it.

Only after items 1--4 close should the numerical proportion be advertised as
an end-to-end Lean theorem.

## Reproduction

From this directory:

```bash
lake build ZetaSeven
lake env lean ZetaSeven/Audit.lean
```

The completed build in this workspace comprised 2,830 jobs.  The audit reports
only the standard foundational axioms already present in the upstream
development:

```text
[propext, Classical.choice, Quot.sound]
```

The source scan

```bash
rg -n '(^|[^[:alnum:]_])(sorry|admit|axiom)([^[:alnum:]_]|$)' ZetaSeven ZetaSeven.lean
```

returns no matches.
