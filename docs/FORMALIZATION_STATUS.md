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

The new library root is `ZetaSeven`.  This repository stores only that
extension; the CI workflow fetches the pinned upstream `Zeta23` source and
overlays these files before rebuilding against exactly the audited base.

## Closed, compiled theorems

| Lean declaration | Mathematical role |
| --- | --- |
| `ZetaSeven.Stability.rank_trace_spectral_gc` | Retains the full spectral `g_c` surplus before the Schur/diagonal relaxation in Claude's multiplicity-aware rank--trace proof. |
| `ZetaSeven.Stability.psi_eq_gc_add_one` | Proves the exact identity `Psi(x) = g_2(x) + 1`. |
| `ZetaSeven.Stability.min_one_sum_sq_sub_one_le_sum_psi` | Proves the scalar spectral energy bridge `min(1, sum (lambda_i-1)^2) <= sum Psi(lambda_i)`. |
| `ZetaSeven.Stability.sum_sq_sub_one_eigenvalues_eq_frob_sub_card` | Converts squared spectral deviation into Frobenius excess for a PSD matrix of normalized trace. |
| `ZetaSeven.Stability.min_one_frob_sub_card_le_spectralDefect` | Matrix form of the local energy bridge. |
| `ZetaSeven.Stability.gram_defect_rank_trace` | Proves the strengthened Gram-matrix inequality `||P+Q||_F^2 >= 4 tr(P+Q)-3r-4b+D(M)`. |
| `ZetaSeven.BlockDefect.min_one_two_mul_upperOffDiagEnergy_le_spectralDefect` | Proves the manuscript's exact `min(1, 2 sum_{i<j} ||M_ij||^2) <= D(M)` inequality, without a unit-diagonal assumption. |
| `Zeta23.ZeroSide.ZeroBlockData.posIndex_simpleQ_le` | Splits off exactly the simple on-line Gram block and proves that the remainder has positive index at most `s₂+p`. |
| `Zeta23.ZeroSide.ZeroBlockData.finite_simple_zero_counting` | Retains the simple-zero Gram defect in the exact finite zero-side count. |
| `ZetaSeven.SimpleBlock.hatAz_simple_defect` | Instantiates the finite defect inequality against the concrete zeta-zero `ZeroConfig/Params` data. |
| `ZetaSeven.SeamDefect.seamA_simple_defect` | Carries the defect through the finite tail perturbation and the passage from `I'` to `(T,2T]`. |
| `ZetaSeven.Assembly.finite_zero_counting` | Checks the finite zero-count bookkeeping after the strengthened matrix inequality. |
| `ZetaSeven.Assembly.Cstar_*` | Checks `C_*`, the `261/262` threshold, both exact block values, and denominator positivity by rational normalization. |
| `ZetaSeven.Assembly.assemble_stability` | Checks the global linear rearrangement, with both error terms explicit. |
| `ZetaSeven.Assembly.assemble_stability_div` | Checks the positive-denominator quotient form. |
| `ZetaSeven.Assembly.sigma_exact_form` | Checks the exact linear-fractional expression with denominator `2660013536538507`. |
| `ZetaSeven.AsymptoticAssembly.assemble_stability_eps` | Converts the defect-preserving source and local inequalities, with two explicit `o(N)` errors, into the epsilon-form proportion statement. |
| `ZetaSeven.AsymptoticAssembly.assemble_Cstar_eps` | Specializes that asymptotic assembly to the exact rational constant `Cstar`. |
| `ZetaSeven.ThmDDefect.simple_lower_c_defect` | Substitutes the Theorem-D trace and Frobenius estimates while retaining an arbitrary favorable defect term. |
| `ZetaSeven.ThmDDefect.thmD_simple_defect_abstract` | Carries the concrete simple-zero Gram spectral defect through the pinned Theorem-D trace/tail hypotheses and packages every remaining source-side error as `o(N)`. |
| `ZetaSeven.WindowEnergy.block_energy_of_sevenPointClaim` | Proves the exact finite consecutive-window inequality: `n` seven-point windows charge every short pair at most twice and every gap at most `1/500`, conditional only on `SevenPointClaim`. |
| `ZetaSeven.Pinching.sum_psi_re_diag_unitary_le_spectralDefect` | Proves the Schur--Horn inequality for the chosen `Psi` penalty in an arbitrary unitary basis. |
| `ZetaSeven.Pinching.sum_spectralDefect_principalBlock_le` | Constructs the block-diagonal unitary from all principal-block eigenbases and proves that the sum of all principal-block defects is at most the full defect for an arbitrary finite sigma-type partition. |
| `ZetaSeven.Pinching.spectralDefect_reindex` | Proves that simultaneous row/column reindexing by any finite equivalence preserves the complete spectral defect. |
| `ZetaSeven.OrderedSimpleZeros.simpleOrdinateAt_strictMono` | Enumerates the actual concrete simple critical-line zero subtype by `Fin (s₁(T))` and proves that the physical ordinates are strictly increasing. |
| `ZetaSeven.OrderedSimpleZeros.normalizedSimpleOrdinateAt_strictMono` | Transfers strict ordering to the paper's normalized coordinate `L(γ-T)/(2π)`. |
| `ZetaSeven.OrderedSimpleZeros.simpleGap_pos` | Proves every adjacent normalized gap in the concrete ordered simple-zero list is positive. |
| `ZetaSeven.OrderedSimpleZeros.orderedSimpleGram_spectralDefect` | Reindexes the actual simple-zero Gram matrix on the increasing `Fin (s₁(T))` index and proves exact preservation of its spectral defect. |
| `ZetaSeven.ShiftedPartitions.sum_full_267_block_spans_le` | Proves that the `S-266` consecutive 267-point blocks charge every adjacent gap at most 266 times. |
| `ZetaSeven.ShiftedPartitions.aggregate_267_shifted_blocks` | Proves the exact finite 267-offset aggregation from residue-fiber pinching hypotheses, including all endpoint and block-error sums. |
| `ZetaSeven.BlockEnergyDefect.defect_lower_of_kernel_energy_approx` | Joins the seven-point block energy to the PSD spectral defect, leaving only an explicit nonnegative finite Gram-to-kernel comparison error. |

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
4. Starting from the now-compiled increasing-ordinate coordinates for the
   actual simple-zero Gram matrix, construct the retained central sublist,
   concrete residue partitions, and endpoint remainders; prove central
   endpoint deletion and the uniform finite Gram-to-kernel
   comparison required by
   `BlockEnergyDefect.defect_lower_of_kernel_energy_approx`.  The finite
   zero-side split, tail seam, abstract Theorem-D source inequality, and
   epsilon-form algebra are already checked.  A concrete top-level
   specialization must still discharge these analytic interfaces.

Only after items 1--4 close should the numerical proportion be advertised as
an end-to-end Lean theorem.

## Reproduction

After overlaying `lean/ZetaSeven`, `lean/ZetaSeven.lean`, and the pinned Lake
files on the upstream commit (the exact procedure is in
`.github/workflows/lean.yml`):

```bash
lake build ZetaSeven
lake env lean ZetaSeven/Audit.lean
```

The full `lake build ZetaSeven` target in this workspace completed 8,851 jobs
for the pinned dependency closure plus the `ZetaSeven` extension.  The audit reports
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
