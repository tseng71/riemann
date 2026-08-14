/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ThmD.WindowCore

/-!
# Exact finite-grid decomposition of the Poisson correlation

The zero-side Gram matrix retains the grid indices `0, ..., d - 1`, whereas
the Poisson identity is a sum over every integer.  This module separates the
two without an asymptotic estimate: the retained finite correlation plus the
correlation on the complementary integer indices is exactly the full Poisson
kernel.  Subsequent endpoint estimates only have to bound the displayed
complementary term.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace ZetaSeven.FinitePoissonDecomposition

open Zeta23

/-- The integer grid indices represented by `Fin d`. -/
def retainedGrid (d : ℕ) : Finset ℤ := Finset.Ico 0 (d : ℤ)

/-- One real Poisson-correlation summand. -/
def gridCorrelation (v : ℝ → ℝ) (L T γ γ' : ℝ) (k : ℤ) : ℝ :=
  AdmWindow.vHatR v (γ - (T + k * (2 * Real.pi / L))) *
    AdmWindow.vHatR v (γ' - (T + k * (2 * Real.pi / L)))

/-- The finite correlation retained by the zero-side matrix. -/
def retainedCorrelation (v : ℝ → ℝ) (L T γ γ' : ℝ) (d : ℕ) : ℝ :=
  ∑ k ∈ retainedGrid d, gridCorrelation v L T γ γ' k

/-- The two omitted endpoint tails, represented as one sum on the complement
of the retained integer interval. -/
def omittedCorrelation (v : ℝ → ℝ) (L T γ γ' : ℝ) (d : ℕ) : ℝ :=
  ∑' k : ↥((↑(retainedGrid d) : Set ℤ)ᶜ),
    gridCorrelation v L T γ γ' k.1

/-- The complement of the retained grid consists exactly of the two endpoint
tails. -/
theorem mem_retainedGrid_compl_iff (d : ℕ) (k : ℤ) :
    k ∈ (↑(retainedGrid d) : Set ℤ)ᶜ ↔
      k < 0 ∨ (d : ℤ) ≤ k := by
  simp only [Set.mem_compl_iff, Finset.mem_coe, retainedGrid,
    Finset.mem_Ico]
  omega

/-- The integer-interval retained sum is exactly the `Fin d` sum used by the
finite Gram matrix. -/
theorem retainedCorrelation_eq_fin (v : ℝ → ℝ) (L T γ γ' : ℝ) (d : ℕ) :
    retainedCorrelation v L T γ γ' d =
      ∑ k : Fin d, gridCorrelation v L T γ γ' (k : ℤ) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => gridCorrelation v L T γ γ' (k : ℤ))]
  unfold retainedCorrelation retainedGrid
  symm
  refine Finset.sum_nbij (fun k : ℕ => (k : ℤ)) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_range] at hk
    rw [Finset.mem_Ico]
    omega
  · intro a ha b hb hab
    simpa using hab
  · intro k hk
    change k ∈ Finset.Ico 0 (d : ℤ) at hk
    rw [Finset.mem_Ico] at hk
    refine ⟨k.toNat, ?_, ?_⟩
    · rw [Finset.mem_range]
      have hlt : (k.toNat : ℤ) < (d : ℤ) := by
        rw [Int.toNat_of_nonneg hk.1]
        exact hk.2
      exact_mod_cast hlt
    · exact Int.toNat_of_nonneg hk.1
  · intro k _
    rfl

/-- Exact retained-plus-omitted decomposition of the full Poisson sum. -/
theorem retained_add_omitted_eq_full {v : ℝ → ℝ} {L w c : ℝ}
    (hW : AdmWindow v L w c) (T γ γ' : ℝ) (d : ℕ) :
    retainedCorrelation v L T γ γ' d +
        omittedCorrelation v L T γ γ' d =
      L * AdmWindow.VPhiR v (γ - γ') := by
  have hfull := hW.hasSum_vHatR_mul T γ γ'
  calc
    retainedCorrelation v L T γ γ' d +
        omittedCorrelation v L T γ γ' d =
      ∑' k : ℤ, gridCorrelation v L T γ γ' k := by
        simpa [retainedCorrelation, omittedCorrelation, gridCorrelation] using
          hfull.summable.sum_add_tsum_compl (s := retainedGrid d)
    _ = L * AdmWindow.VPhiR v (γ - γ') := hfull.tsum_eq

/-- Subtractive form used when comparing a finite Gram entry with the full
kernel. -/
theorem retained_eq_full_sub_omitted {v : ℝ → ℝ} {L w c : ℝ}
    (hW : AdmWindow v L w c) (T γ γ' : ℝ) (d : ℕ) :
    retainedCorrelation v L T γ γ' d =
      L * AdmWindow.VPhiR v (γ - γ') -
        omittedCorrelation v L T γ γ' d := by
  linarith [retained_add_omitted_eq_full hW T γ γ' d]

/-- The omitted correlation is bounded by the sum of the absolute omitted
summands.  Summability is inherited directly from the Poisson series. -/
theorem abs_omittedCorrelation_le_tsum_abs {v : ℝ → ℝ} {L w c : ℝ}
    (hW : AdmWindow v L w c) (T γ γ' : ℝ) (d : ℕ) :
    |omittedCorrelation v L T γ γ' d| ≤
      ∑' k : ↥((↑(retainedGrid d) : Set ℤ)ᶜ),
        |gridCorrelation v L T γ γ' k.1| := by
  have hs : Summable (fun k : ℤ => gridCorrelation v L T γ γ' k) :=
    (hW.hasSum_vHatR_mul T γ γ').summable
  unfold omittedCorrelation
  change
    ‖∑' k : ↥((↑(retainedGrid d) : Set ℤ)ᶜ),
        gridCorrelation v L T γ γ' k.1‖ ≤
      ∑' k : ↥((↑(retainedGrid d) : Set ℤ)ᶜ),
        ‖gridCorrelation v L T γ γ' k.1‖
  exact norm_tsum_le_tsum_norm
    (hs.subtype ((↑(retainedGrid d) : Set ℤ)ᶜ)).norm

/-- Pointwise fourth-order product decay for a correlation summand.  This is
the analytic input for summing the two omitted endpoint tails. -/
theorem abs_gridCorrelation_mul_sq_le {v : ℝ → ℝ} {L w c : ℝ}
    (hW : AdmWindow v L w c) (T γ γ' : ℝ) (k : ℤ) :
    |gridCorrelation v L T γ γ' k| *
          (γ - (T + k * (2 * Real.pi / L))) ^ 2 *
          (γ' - (T + k * (2 * Real.pi / L))) ^ 2 ≤
      (c / w) ^ 2 := by
  have hγ := hW.abs_vHatR_mul_sq_le
    (γ - (T + k * (2 * Real.pi / L)))
  have hγ' := hW.abs_vHatR_mul_sq_le
    (γ' - (T + k * (2 * Real.pi / L)))
  have hcw : 0 ≤ c / w := div_nonneg hW.c_nonneg hW.w_pos.le
  calc
    |gridCorrelation v L T γ γ' k| *
          (γ - (T + k * (2 * Real.pi / L))) ^ 2 *
          (γ' - (T + k * (2 * Real.pi / L))) ^ 2 =
        (|AdmWindow.vHatR v
              (γ - (T + k * (2 * Real.pi / L)))| *
            (γ - (T + k * (2 * Real.pi / L))) ^ 2) *
          (|AdmWindow.vHatR v
              (γ' - (T + k * (2 * Real.pi / L)))| *
            (γ' - (T + k * (2 * Real.pi / L))) ^ 2) := by
              rw [gridCorrelation, abs_mul]
              ring
    _ ≤ (c / w) * (c / w) :=
      mul_le_mul hγ hγ' (by positivity) hcw
    _ = (c / w) ^ 2 := by ring

end ZetaSeven.FinitePoissonDecomposition
