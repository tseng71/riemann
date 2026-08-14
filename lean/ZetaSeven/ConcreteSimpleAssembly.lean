/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0
-/
import ZetaSeven.ConcreteShiftedPinching

/-!
# Concrete finite assembly on the ordered simple-zero Gram matrix

This module identifies the local gaps in every consecutive 267-point block
with one global increasing-ordinate gap sequence.  It then combines the
local Gram-to-kernel comparison hypotheses with the concrete 267-shift
pinching theorem.  The resulting finite inequality has no abstract
partition or pinching hypotheses left.
-/

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset
open scoped ComplexOrder BigOperators

namespace ZetaSeven.ConcreteSimpleAssembly

open Zeta23
open Zeta23.ZeroSide
open RHLinalg
open ZetaSeven.Stability
open ZetaSeven.SevenPointSpec
open ZetaSeven.WindowEnergy
open ZetaSeven.OrderedSimpleZeros
open ZetaSeven.ConcreteBlocks
open ZetaSeven.ConcreteShiftedPinching

variable (Z : ZeroConfig) (T : ℝ) (P : Params)

/-- The global increasing-ordinate normalized gap sequence, extended by
zero past its finite natural range. -/
def orderedSimpleGapNat (hconj : PhiHatConj T P) (k : ℕ) : ℝ :=
  if hk : k < Z.s1 T - 1 then
    simpleGap Z T P hconj ⟨k, hk⟩
  else 0

lemma orderedSimpleGapNat_nonneg (hconj : PhiHatConj T P)
    (hL : 0 < P.L T) :
    ∀ k, 0 ≤ orderedSimpleGapNat Z T P hconj k := by
  intro k
  unfold orderedSimpleGapNat
  split_ifs with hk
  · exact simpleGap_nonneg Z T P hconj hL ⟨k, hk⟩
  · exact le_rfl

/-- A global gap at position `k + a` is definitionally the corresponding
gap inside the full block beginning at `k`. -/
lemma orderedSimpleGapNat_add_eq_orderedBlockGap
    (hconj : PhiHatConj T P) (k : ℕ) (hk : k + 267 ≤ Z.s1 T)
    {a : ℕ} (ha : a < 266) :
    orderedSimpleGapNat Z T P hconj (k + a) =
      orderedBlockGap Z T P hconj k hk a := by
  rw [orderedBlockGap_of_lt Z T P hconj k hk ha]
  unfold orderedSimpleGapNat simpleGap
  rw [dif_pos (by omega)]

/-- Therefore the 266-gap pressure term in a full block is exactly the
corresponding segment of the global gap sequence. -/
lemma sum_orderedSimpleGapNat_eq_orderedBlockGap
    (hconj : PhiHatConj T P) (k : ℕ) (hk : k + 267 ≤ Z.s1 T) :
    (∑ a ∈ range 266, orderedSimpleGapNat Z T P hconj (k + a)) =
      ∑ a ∈ range 266, orderedBlockGap Z T P hconj k hk a := by
  apply Finset.sum_congr rfl
  intro a ha
  exact orderedSimpleGapNat_add_eq_orderedBlockGap Z T P hconj k hk
    (Finset.mem_range.mp ha)

/-- Every initial segment of the global ordered gap sequence telescopes to
the separation of its two endpoint coordinates. -/
lemma sum_orderedSimpleGapNat_eq_sub
    (hconj : PhiHatConj T P) {n : ℕ} (hn : n < Z.s1 T) :
    (∑ j ∈ range n, orderedSimpleGapNat Z T P hconj j) =
      normalizedSimpleOrdinateAt Z T P hconj ⟨n, hn⟩ -
        normalizedSimpleOrdinateAt Z T P hconj ⟨0, by omega⟩ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sum_range_succ]
      rw [ih (by omega)]
      rw [orderedSimpleGapNat, dif_pos (by omega)]
      unfold simpleGap
      ring_nf

/-- The complete global gap sum is exactly the normalized span from the
first ordered simple zero to the last. -/
theorem sum_orderedSimpleGapNat_eq_endpointSpan
    (hconj : PhiHatConj T P) (hS : 2 ≤ Z.s1 T) :
    (∑ j ∈ range (Z.s1 T - 1), orderedSimpleGapNat Z T P hconj j) =
      normalizedSimpleOrdinateAt Z T P hconj
          ⟨Z.s1 T - 1, by omega⟩ -
        normalizedSimpleOrdinateAt Z T P hconj ⟨0, by omega⟩ := by
  simpa using
    (sum_orderedSimpleGapNat_eq_sub Z T P hconj
      (n := Z.s1 T - 1) (by omega))

/-- **Concrete finite simple-zero assembly.**  For the actual ordered
simple-zero Gram matrix, the 267 shifted partitions and all endpoint
remainders have been discharged.  The remaining local inputs are precisely
the displayed per-block Gram-to-kernel comparison errors and the explicit
seven-point certificate claim. -/
theorem orderedSimpleGram_finite_267_assembly
    (hseven : SevenPointClaim) (hconj : PhiHatConj T P)
    (hL : 0 < P.L T) (hS : 267 ≤ Z.s1 T)
    (E : ℕ → ℝ) (hE : ∀ k, 0 ≤ E k)
    (happrox : ∀ k (hk : k + 267 ≤ Z.s1 T),
      blockPairEnergy (orderedBlockGap Z T P hconj k hk) 261 - E k ≤
        2 * ZetaSeven.BlockDefect.upperOffDiagEnergy
          (orderedBlockGram Z T P hconj k hk)) :
    ((Z.s1 T - 266 : ℕ) : ℝ) * (261 * ZetaSeven.Assembly.Cstar)
        - (266 / 500 : ℝ) *
            (∑ j ∈ range (Z.s1 T - 1),
              orderedSimpleGapNat Z T P hconj j)
        - ∑ k ∈ range (Z.s1 T - 266), E k
      ≤ 267 * spectralDefect
          (orderedSimpleGram_posSemidef Z T P hconj) := by
  apply aggregate_267_consecutiveBlock_defects hS
    (orderedSimpleGram_posSemidef Z T P hconj)
    ZetaSeven.Assembly.Cstar (orderedSimpleGapNat Z T P hconj) E
    (orderedSimpleGapNat_nonneg Z T P hconj hL)
  intro k hkRange
  have hk : k + 267 ≤ Z.s1 T := by
    have hk' := Finset.mem_range.mp hkRange
    omega
  have hlocal := orderedBlock_defect_lower_of_kernel_energy_approx
    Z T P hseven hconj hL k hk (E k) (hE k) (happrox k hk)
  rw [sum_orderedSimpleGapNat_eq_orderedBlockGap Z T P hconj k hk]
  simpa [blockDefectAt, hk, orderedBlockGram] using hlocal

/-- The concrete block assembly inserted into the exact finite zero-side
counting inequality.  What remains after this theorem is analytic: bounding
the displayed trace/Frobenius source, the total normalized gap length, and
the summed Gram-to-kernel comparison error. -/
theorem finite_simple_count_with_267_assembly
    (hseven : SevenPointClaim) (hconj : PhiHatConj T P)
    (hreal : PhiHatReal T P) (hPois : PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2) (hL : 0 < P.L T)
    (hS : 267 ≤ Z.s1 T)
    (E : ℕ → ℝ) (hE : ∀ k, 0 ≤ E k)
    (happrox : ∀ k (hk : k + 267 ≤ Z.s1 T),
      blockPairEnergy (orderedBlockGap Z T P hconj k hk) 261 - E k ≤
        2 * ZetaSeven.BlockDefect.upperOffDiagEnergy
          (orderedBlockGram Z T P hconj k hk)) :
    4 * rtrace (P.hat T (Z.Az P T))
        - frobSq (P.hat T (Z.Az P T))
        - 2 * (Z.NIprime T : ℝ)
        + (((Z.s1 T - 266 : ℕ) : ℝ) *
              (261 * ZetaSeven.Assembly.Cstar)
            - (266 / 500 : ℝ) *
                (∑ j ∈ range (Z.s1 T - 1),
                  orderedSimpleGapNat Z T P hconj j)
            - ∑ k ∈ range (Z.s1 T - 266), E k) / 267
      ≤ (Z.s1 T : ℝ) := by
  have hsource := ZetaSeven.SimpleBlock.hatAz_simple_defect
    Z T P hconj hreal hPois hc
  rw [← orderedSimpleGram_spectralDefect Z T P hconj] at hsource
  have hlocal := orderedSimpleGram_finite_267_assembly
    Z T P hseven hconj hL hS E hE happrox
  linarith

end ZetaSeven.ConcreteSimpleAssembly
