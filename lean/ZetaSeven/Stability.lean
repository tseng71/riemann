/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0
-/
/-
# Spectral stability retained by the rank--trace argument

This file records the matrix-theoretic part of the seven-point refinement.
Unlike `Zeta23.ZeroSide.RankTraceMult.rank_trace_mult`, the first theorem below
does not replace the spectral `g_c` sum by a diagonal lower bound.  Retaining
that nonnegative surplus is exactly what the stability refinement needs.
-/
import Zeta23.ZeroSide.RankTraceMult

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset
open scoped ComplexOrder BigOperators
open Zeta23.ZeroSide.RankTraceMult

namespace ZetaSeven.Stability

open RHLinalg

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The rank--trace inequality before the Schur/diagonal relaxation.

For `P` positive semidefinite and `Q` Hermitian with at most `b` positive
eigenvalues, the full spectral convex surplus `sum g_c(lambda_i(P))` survives.
-/
theorem rank_trace_spectral_gc {P Q : Matrix n n 𝕜}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {b : ℕ} (hb : posIndex hQ ≤ b) {c : ℝ} (hc : 0 < c) :
    c * rtrace P + (∑ i, gc c (hP.1.eigenvalues i))
        + 2 * c * rtrace Q - c ^ 2 * b ≤ frobSq (P + Q) := by
  classical
  set Qp := hermPosPart hQ with hQp_def
  set Qm := hermNegPart hQ with hQm_def
  have hQdec : Q = Qp - Qm := (hermPosPart_sub_hermNegPart hQ).symm
  have hQp_psd : Qp.PosSemidef := hermPosPart_posSemidef hQ
  have hQm_psd : Qm.PosSemidef := hermNegPart_posSemidef hQ
  have hQpQm : Qp * Qm = 0 := hermPosPart_mul_hermNegPart hQ
  set d := Fintype.card n
  set p : Fin d → ℝ := hP.isHermitian.eigenvalues₀
  set m : Fin d → ℝ := hQm_psd.isHermitian.eigenvalues₀
  have hp_nn : ∀ k, 0 ≤ p k := fun k => by
    rw [show p k = hP.isHermitian.eigenvalues (eigEquiv k) from
      (eigenvalues_eigEquiv hP.isHermitian k).symm]
    exact hP.eigenvalues_nonneg _
  have hm_nn : ∀ k, 0 ≤ m k := fun k => by
    rw [show m k = hQm_psd.isHermitian.eigenvalues (eigEquiv k) from
      (eigenvalues_eigEquiv hQm_psd.isHermitian k).symm]
    exact hQm_psd.eigenvalues_nonneg _
  have htraceP : rtrace P = ∑ k, p k := by
    rw [rtrace_eq_sum_eigenvalues hP.isHermitian]
    exact sum_eigenvalues_reindex hP.isHermitian id
  have htraceQm : rtrace Qm = ∑ k, m k := by
    rw [rtrace_eq_sum_eigenvalues hQm_psd.isHermitian]
    exact sum_eigenvalues_reindex hQm_psd.isHermitian id
  have hfrobP : frobSq P = ∑ k, (p k) ^ 2 := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues hP.isHermitian]
    exact sum_eigenvalues_reindex hP.isHermitian (· ^ 2)
  have hfrobQm : frobSq Qm = ∑ k, (m k) ^ 2 := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues hQm_psd.isHermitian]
    exact sum_eigenvalues_reindex hQm_psd.isHermitian (· ^ 2)
  have hgcP : (∑ i, gc c (hP.1.eigenvalues i)) = ∑ k, gc c (p k) :=
    sum_eigenvalues_reindex hP.isHermitian (gc c)
  have hexpand : frobSq (P + Q)
      = frobSq P + 2 * RCLike.re (P * Qp).trace
        - 2 * RCLike.re (P * Qm).trace + frobSq Qp + frobSq Qm := by
    have h1 : frobSq (-Qm) = frobSq Qm := by
      unfold frobSq
      rw [conjTranspose_neg, neg_mul_neg]
    have h2 : RCLike.re (Qp * -Qm).trace = 0 := by
      rw [mul_neg, hQpQm]
      simp
    rw [hQdec, frobSq_add_hermitian hP.isHermitian
        (hQp_psd.isHermitian.sub hQm_psd.isHermitian),
      sub_eq_add_neg Qp Qm,
      frobSq_add_hermitian hQp_psd.isHermitian hQm_psd.isHermitian.neg,
      h1, h2, mul_add, mul_neg, trace_add, trace_neg, map_add, map_neg]
    ring
  have hPQp : 0 ≤ RCLike.re (P * Qp).trace :=
    trace_mul_nonneg_of_posSemidef hP hQp_psd
  have hvN : RCLike.re (P * Qm).trace ≤ ∑ k, p k * m k :=
    vonNeumann_trace_ineq hP.isHermitian hQm_psd.isHermitian
  have hstep4 : ∑ k, (p k - m k) ^ 2
      ≤ frobSq P - 2 * RCLike.re (P * Qm).trace + frobSq Qm := by
    have hsplit : ∑ k, (p k - m k) ^ 2
        = ∑ k, (p k) ^ 2 - 2 * ∑ k, p k * m k + ∑ k, (m k) ^ 2 := by
      simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.mul_sum, mul_assoc]
    rw [hsplit, hfrobP, hfrobQm]
    linarith
  have hstep5 : c * rtrace P + (∑ k, gc c (p k)) - 2 * c * rtrace Qm
      ≤ ∑ k, (p k - m k) ^ 2 := by
    rw [htraceP, htraceQm]
    exact sum_sq_sub_ge_gc hp_nn hm_nn hc.le
  have hstep6 : 2 * c * rtrace Qp - c ^ 2 * b ≤ frobSq Qp := by
    rw [hQp_def, rtrace_hermPosPart, frobSq_hermPosPart]
    refine sum_sq_lower_of_card_pos_le ?_ c
    calc
      #{i | (hQ.eigenvalues i)⁺ ≠ 0} = #{i | 0 < hQ.eigenvalues i} := by
        congr 1
        ext i
        simp [posPart_eq_zero, not_le]
      _ ≤ b := hb
  have htraceQ : 2 * c * rtrace Q =
      2 * c * rtrace Qp - 2 * c * rtrace Qm := by
    rw [hQdec, rtrace_sub]
    ring
  linarith [hstep4, hstep5, hstep6, hPQp, hexpand, htraceQ, hgcP]

/-! ## The defect used by the seven-point refinement -/

/-- The piecewise spectral penalty from the research memo. -/
def psi (x : ℝ) : ℝ := if x ≤ 2 then (x - 1) ^ 2 else 2 * x - 3

/-- `psi` is `g_2 + 1`; this identity is what connects the new penalty to the
existing multiplicity-aware rank--trace machinery. -/
lemma psi_eq_gc_add_one (x : ℝ) : psi x = gc 2 x + 1 := by
  rcases le_or_gt x 2 with hx | hx
  · rw [psi, if_pos hx, gc_of_le hx]
    ring
  · rw [psi, if_neg (not_le.mpr hx), gc_of_ge hx.le]
    ring

lemma psi_nonneg (x : ℝ) : 0 ≤ psi x := by
  rcases le_or_gt x 2 with h | h
  · rw [psi, if_pos h]
    positivity
  · rw [psi, if_neg (not_le.mpr h)]
    linarith

lemma one_le_psi_of_two_le {x : ℝ} (hx : 2 ≤ x) : 1 ≤ psi x := by
  rcases hx.eq_or_lt with rfl | h
  · norm_num [psi]
  · rw [psi, if_neg (not_le.mpr h)]
    linarith

/-- Spectral form of the energy lower bound: the defect is at least the
smaller of one and the total squared distance of the eigenvalues from one. -/
theorem min_one_sum_sq_sub_one_le_sum_psi
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) :
    min 1 (∑ i, (x i - 1) ^ 2) ≤ ∑ i, psi (x i) := by
  classical
  by_cases hall : ∀ i, x i ≤ 2
  · have heq : (∑ i, psi (x i)) = ∑ i, (x i - 1) ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [psi, hall i]
    rw [heq]
    exact min_le_right _ _
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    calc
      min 1 (∑ i, (x i - 1) ^ 2) ≤ 1 := min_le_left _ _
      _ ≤ psi (x i) := one_le_psi_of_two_le hi.le
      _ ≤ ∑ j, psi (x j) := Finset.single_le_sum
        (fun j _ => psi_nonneg (x j)) (Finset.mem_univ i)

/-- Sum of `psi` over the spectrum of a positive semidefinite matrix. -/
def spectralDefect {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι 𝕜} (hM : M.PosSemidef) : ℝ :=
  ∑ i, psi (hM.1.eigenvalues i)

lemma spectralDefect_eq_sum_gc_add_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι 𝕜} (hM : M.PosSemidef) :
    spectralDefect hM = (∑ i, gc 2 (hM.1.eigenvalues i)) + Fintype.card ι := by
  unfold spectralDefect
  simp_rw [psi_eq_gc_add_one, Finset.sum_add_distrib]
  simp

/-- For a PSD matrix of trace equal to its dimension, the squared spectral
distance from the identity is its Frobenius excess. -/
lemma sum_sq_sub_one_eigenvalues_eq_frob_sub_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι 𝕜} (hM : M.PosSemidef)
    (htrace : rtrace M = (Fintype.card ι : ℝ)) :
    (∑ i, (hM.1.eigenvalues i - 1) ^ 2)
      = frobSq M - Fintype.card ι := by
  have heigsum : (∑ i, hM.1.eigenvalues i) = (Fintype.card ι : ℝ) := by
    rw [← rtrace_eq_sum_eigenvalues hM.1]
    exact htrace
  have heigsq : (∑ i, (hM.1.eigenvalues i) ^ 2) = frobSq M := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues hM.1]
  calc
    (∑ i, (hM.1.eigenvalues i - 1) ^ 2)
        = (∑ i, (hM.1.eigenvalues i) ^ 2)
          - 2 * (∑ i, hM.1.eigenvalues i) + Fintype.card ι := by
            simp only [sub_sq, Finset.sum_sub_distrib, Finset.sum_add_distrib,
              Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring_nf
    _ = frobSq M - Fintype.card ι := by rw [heigsum, heigsq]; ring

/-- Matrix form of the local energy bridge. -/
theorem min_one_frob_sub_card_le_spectralDefect
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι 𝕜} (hM : M.PosSemidef)
    (htrace : rtrace M = (Fintype.card ι : ℝ)) :
    min 1 (frobSq M - Fintype.card ι) ≤ spectralDefect hM := by
  rw [← sum_sq_sub_one_eigenvalues_eq_frob_sub_card hM htrace]
  exact min_one_sum_sq_sub_one_le_sum_psi _

/-- Exact strengthened `c = 2` rank--trace inequality for a column Gram
matrix.  It is the matrix-level stability statement used in the refinement.

The only normalization hypothesis is `tr(WW*) ≤ number_of_columns`; in the
application this follows from the column norm bounds.
-/
theorem gram_defect_rank_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix n ι 𝕜) {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian)
    {b : ℕ} (hb : posIndex hQ ≤ b)
    (htrace : rtrace (W * Wᴴ) ≤ (Fintype.card ι : ℝ)) :
    4 * rtrace (W * Wᴴ + Q) - 3 * (Fintype.card ι : ℝ) - 4 * (b : ℝ)
        + spectralDefect (Matrix.posSemidef_conjTranspose_mul_self W)
      ≤ frobSq (W * Wᴴ + Q) := by
  let hP : (W * Wᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose W
  let hM : (Wᴴ * W).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self W
  have hspectral := rank_trace_spectral_gc hP hQ hb (c := 2) (by norm_num)
  have htransfer : (∑ i, gc 2 (hP.1.eigenvalues i)) =
      ∑ j, gc 2 (hM.1.eigenvalues j) :=
    sum_eigenvalues_comm W (gc 2) (gc_zero (by norm_num))
  have hdefect := spectralDefect_eq_sum_gc_add_card hM
  rw [htransfer] at hspectral
  rw [rtrace_add, hdefect]
  norm_num at hspectral ⊢
  linarith

end ZetaSeven.Stability
