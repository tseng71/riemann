/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0
-/
import ZetaSeven.Stability

/-!
# From spectral defect to off-diagonal Gram energy

This file closes the finite-dimensional bridge used in the block argument.
For a positive semidefinite matrix `M`, its spectral defect dominates the
smaller of one and the ordered off-diagonal Frobenius energy.  For a
Hermitian matrix the latter is the paper's `2 * sum_{i<j} ‖M i j‖²`.

No trace or unit-diagonal normalization is needed: the missing diagonal
contribution is a sum of squares `‖M i i - 1‖²`.
-/

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset
open scoped ComplexOrder BigOperators

namespace ZetaSeven.BlockDefect

open RHLinalg
open ZetaSeven.Stability

variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sum of squared norms of all ordered off-diagonal entries.  For a
Hermitian matrix this counts every unordered pair twice. -/
def orderedOffDiagEnergy (M : Matrix ι ι 𝕜) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset ι).offDiag, ‖M p.1 p.2‖ ^ 2

/-- The upper-triangular version of the off-diagonal energy. -/
def upperOffDiagEnergy [LinearOrder ι] (M : Matrix ι ι 𝕜) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset ι).offDiag with p.1 < p.2,
    ‖M p.1 p.2‖ ^ 2

private lemma frobSq_eq_sum_norm_sq (M : Matrix ι ι 𝕜) :
    frobSq M = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  unfold frobSq
  simp only [trace, diag_apply, mul_apply, conjTranspose_apply, map_sum,
    RCLike.star_def]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- Frobenius energy splits exactly into diagonal and ordered off-diagonal
energy. -/
lemma frobSq_eq_diag_add_orderedOffDiagEnergy (M : Matrix ι ι 𝕜) :
    frobSq M = (∑ i, ‖M i i‖ ^ 2) + orderedOffDiagEnergy M := by
  rw [frobSq_eq_sum_norm_sq]
  unfold orderedOffDiagEnergy
  simp_rw [← Finset.sum_product']
  rw [← Finset.diag_union_offDiag,
    Finset.sum_union (Finset.disjoint_diag_offDiag _), Finset.sum_diag]

/-- For a Hermitian matrix the ordered energy is twice the strictly upper
triangular energy, matching the convention in the manuscript. -/
lemma orderedOffDiagEnergy_eq_two_mul_upperOffDiagEnergy
    [LinearOrder ι] {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) :
    orderedOffDiagEnergy M = 2 * upperOffDiagEnergy M := by
  classical
  let s : Finset (ι × ι) := (Finset.univ : Finset ι).offDiag
  let upper := s.filter fun p => p.1 < p.2
  let lower := s.filter fun p => p.2 < p.1
  have hpartition : upper ∪ lower = s := by
    ext p
    simp only [upper, lower, Finset.mem_union, Finset.mem_filter]
    constructor
    · aesop
    · intro hp
      exact Or.imp (fun h => ⟨hp, h⟩) (fun h => ⟨hp, h⟩)
        (lt_or_gt_of_ne (Finset.mem_offDiag.mp hp).2.2)
  have hdisj : Disjoint upper lower := by
    rw [Finset.disjoint_left]
    intro p hpUpper hpLower
    exact lt_asymm (Finset.mem_filter.mp hpUpper).2
      (Finset.mem_filter.mp hpLower).2
  have hlower :
      (∑ p ∈ lower, ‖M p.1 p.2‖ ^ 2)
        = ∑ p ∈ upper, ‖M p.1 p.2‖ ^ 2 := by
    refine Finset.sum_equiv (Equiv.prodComm ι ι) ?_ ?_
    · intro p
      simp [lower, upper, s, ne_comm]
    · intro p hp
      simp only [Equiv.prodComm_apply]
      rw [← hM.apply p.1 p.2, norm_star]
      rfl
  unfold orderedOffDiagEnergy upperOffDiagEnergy
  change (∑ p ∈ s, ‖M p.1 p.2‖ ^ 2) = _
  rw [← hpartition, Finset.sum_union hdisj, hlower]
  change (∑ p ∈ upper, ‖M p.1 p.2‖ ^ 2)
      + ∑ p ∈ upper, ‖M p.1 p.2‖ ^ 2 = _
  ring

private lemma rtrace_eq_sum_re_diag (M : Matrix ι ι 𝕜) :
    rtrace M = ∑ i, RCLike.re (M i i) := by
  unfold rtrace Matrix.trace
  rw [map_sum]
  simp

/-- The ordered off-diagonal energy is at most the squared spectral distance
from the identity.  The proof is entrywise and does not assume normalized
diagonal entries. -/
lemma orderedOffDiagEnergy_le_frobSq_sub_two_trace_add_card
    (M : Matrix ι ι 𝕜) :
    orderedOffDiagEnergy M
      ≤ frobSq M - 2 * rtrace M + Fintype.card ι := by
  have hdiag : 2 * rtrace M - Fintype.card ι ≤ ∑ i, ‖M i i‖ ^ 2 := by
    calc
      2 * rtrace M - Fintype.card ι
          = ∑ i, (2 * RCLike.re (M i i) - 1) := by
              rw [rtrace_eq_sum_re_diag, Finset.mul_sum,
                Finset.sum_sub_distrib]
              simp
      _ ≤ ∑ i, ‖M i i‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [RCLike.norm_sq_eq_def]
        nlinarith [sq_nonneg (RCLike.re (M i i) - 1),
          sq_nonneg (RCLike.im (M i i))]
  have hsplit := frobSq_eq_diag_add_orderedOffDiagEnergy M
  linarith

/-- Without any trace normalization, the total squared spectral distance
from one is `‖M‖_F² - 2 tr M + dim`. -/
lemma sum_sq_sub_one_eigenvalues_eq_frobSq_sub_two_trace_add_card
    {M : Matrix ι ι 𝕜} (hM : M.PosSemidef) :
    (∑ i, (hM.1.eigenvalues i - 1) ^ 2)
      = frobSq M - 2 * rtrace M + Fintype.card ι := by
  have heigsum : (∑ i, hM.1.eigenvalues i) = rtrace M := by
    rw [← rtrace_eq_sum_eigenvalues hM.1]
  have heigsq : (∑ i, (hM.1.eigenvalues i) ^ 2) = frobSq M := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues hM.1]
  calc
    (∑ i, (hM.1.eigenvalues i - 1) ^ 2)
        = (∑ i, (hM.1.eigenvalues i) ^ 2)
          - 2 * (∑ i, hM.1.eigenvalues i) + Fintype.card ι := by
            simp only [sub_sq, Finset.sum_sub_distrib, Finset.sum_add_distrib,
              Finset.mul_sum, Finset.sum_const, Finset.card_univ,
              nsmul_eq_mul]
            ring_nf
    _ = frobSq M - 2 * rtrace M + Fintype.card ι := by
      rw [heigsum, heigsq]

/-- Paper-level block-defect inequality, with the off-diagonal energy written
as an ordered sum.  For Hermitian `M` this is exactly
`min 1 (2 * sum_{i<j} ‖M i j‖²) ≤ tr Ψ(M)`. -/
theorem min_one_orderedOffDiagEnergy_le_spectralDefect
    {M : Matrix ι ι 𝕜} (hM : M.PosSemidef) :
    min 1 (orderedOffDiagEnergy M) ≤ spectralDefect hM := by
  calc
    min 1 (orderedOffDiagEnergy M)
        ≤ min 1 (frobSq M - 2 * rtrace M + Fintype.card ι) :=
          min_le_min le_rfl
            (orderedOffDiagEnergy_le_frobSq_sub_two_trace_add_card M)
    _ = min 1 (∑ i, (hM.1.eigenvalues i - 1) ^ 2) := by
      rw [sum_sq_sub_one_eigenvalues_eq_frobSq_sub_two_trace_add_card hM]
    _ ≤ spectralDefect hM := min_one_sum_sq_sub_one_le_sum_psi _

/-- The exact `2 * sum_{i<j}` form of the paper's block-defect lemma. -/
theorem min_one_two_mul_upperOffDiagEnergy_le_spectralDefect
    [LinearOrder ι] {M : Matrix ι ι 𝕜} (hM : M.PosSemidef) :
    min 1 (2 * upperOffDiagEnergy M) ≤ spectralDefect hM := by
  rw [← orderedOffDiagEnergy_eq_two_mul_upperOffDiagEnergy hM.1]
  exact min_one_orderedOffDiagEnergy_le_spectralDefect hM

end ZetaSeven.BlockDefect
