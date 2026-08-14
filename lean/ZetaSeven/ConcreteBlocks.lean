/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0
-/
import ZetaSeven.OrderedSimpleZeros
import ZetaSeven.BlockEnergyDefect

/-!
# Concrete 267-point blocks of the ordered simple-zero Gram matrix

This module specializes the generic local seven-point bridge to actual
consecutive principal blocks of the increasing-ordinate simple-zero Gram
matrix.  It defines the normalized adjacent gaps, proves their positivity
and telescoping identities, and leaves only the displayed finite
Gram-to-kernel comparison error as an analytic input to each block theorem.
-/

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset
open scoped ComplexOrder BigOperators

namespace ZetaSeven.ConcreteBlocks

open Zeta23
open Zeta23.ZeroSide
open ZetaSeven.Stability
open ZetaSeven.WindowEnergy
open ZetaSeven.SevenPointSpec
open ZetaSeven.OrderedSimpleZeros

/-- The positions of a full 267-point consecutive block. -/
def blockIndex {S : ℕ} (k : ℕ) (hk : k + 267 ≤ S) : Fin 267 → Fin S :=
  fun i => ⟨k + i, by omega⟩

lemma blockIndex_injective {S : ℕ} (k : ℕ) (hk : k + 267 ≤ S) :
    Function.Injective (blockIndex k hk) := by
  intro i j hij
  apply Fin.ext
  have := congrArg Fin.val hij
  simp only [blockIndex] at this
  omega

/-- A concrete consecutive 267-by-267 principal block. -/
def consecutivePrincipalBlock
    {𝕜 : Type*} [RCLike 𝕜] {S : ℕ}
    (M : Matrix (Fin S) (Fin S) 𝕜) (k : ℕ) (hk : k + 267 ≤ S) :
    Matrix (Fin 267) (Fin 267) 𝕜 :=
  M.submatrix (blockIndex k hk) (blockIndex k hk)

theorem consecutivePrincipalBlock_posSemidef
    {𝕜 : Type*} [RCLike 𝕜] {S : ℕ}
    {M : Matrix (Fin S) (Fin S) 𝕜} (hM : M.PosSemidef)
    (k : ℕ) (hk : k + 267 ≤ S) :
    (consecutivePrincipalBlock M k hk).PosSemidef :=
  hM.submatrix (blockIndex k hk)

variable (Z : ZeroConfig) (T : ℝ) (P : Params)

/-- The actual 267-point principal Gram block beginning at increasing
simple-zero position `k`. -/
def orderedBlockGram (hconj : PhiHatConj T P)
    (k : ℕ) (hk : k + 267 ≤ Z.s1 T) :
    Matrix (Fin 267) (Fin 267) ℂ :=
  consecutivePrincipalBlock
    (orderedSimpleGram Z T P hconj) k hk

theorem orderedBlockGram_posSemidef (hconj : PhiHatConj T P)
    (k : ℕ) (hk : k + 267 ≤ Z.s1 T) :
    (orderedBlockGram Z T P hconj k hk).PosSemidef :=
  consecutivePrincipalBlock_posSemidef
    (orderedSimpleGram_posSemidef Z T P hconj) k hk

/-- The 266 normalized adjacent gaps in one concrete full block, extended by
zero outside its used range so it can feed the generic finite-window theorem. -/
def orderedBlockGap (hconj : PhiHatConj T P)
    (k : ℕ) (hk : k + 267 ≤ Z.s1 T) (a : ℕ) : ℝ :=
  if ha : a < 266 then
    normalizedSimpleOrdinateAt Z T P hconj ⟨k + a + 1, by omega⟩ -
      normalizedSimpleOrdinateAt Z T P hconj ⟨k + a, by omega⟩
  else 0

lemma orderedBlockGap_of_lt (hconj : PhiHatConj T P)
    (k : ℕ) (hk : k + 267 ≤ Z.s1 T) {a : ℕ} (ha : a < 266) :
    orderedBlockGap Z T P hconj k hk a =
      normalizedSimpleOrdinateAt Z T P hconj ⟨k + a + 1, by omega⟩ -
        normalizedSimpleOrdinateAt Z T P hconj ⟨k + a, by omega⟩ := by
  simp [orderedBlockGap, ha]

lemma orderedBlockGap_nonneg (hconj : PhiHatConj T P)
    (hL : 0 < P.L T) (k : ℕ) (hk : k + 267 ≤ Z.s1 T) :
    ∀ a, 0 ≤ orderedBlockGap Z T P hconj k hk a := by
  intro a
  unfold orderedBlockGap
  split_ifs with ha
  · exact (sub_pos.mpr
      ((normalizedSimpleOrdinateAt_strictMono Z T P hconj hL)
        (by simp))).le
  · exact le_rfl

/-- Consecutive normalized gaps telescope to the normalized separation of
their endpoints inside a concrete full block. -/
lemma sum_orderedBlockGap_eq_sub (hconj : PhiHatConj T P)
    (k : ℕ) (hk : k + 267 ≤ Z.s1 T) {b n : ℕ} (hbn : b + n ≤ 266) :
    (∑ a ∈ range n, orderedBlockGap Z T P hconj k hk (b + a)) =
      normalizedSimpleOrdinateAt Z T P hconj ⟨k + b + n, by omega⟩ -
        normalizedSimpleOrdinateAt Z T P hconj ⟨k + b, by omega⟩ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sum_range_succ]
      rw [orderedBlockGap_of_lt Z T P hconj k hk (by omega)]
      rw [ih (by omega)]
      ring_nf

/-- The gap pressure term of a full block is exactly its normalized span. -/
lemma sum_orderedBlockGap_eq_span (hconj : PhiHatConj T P)
    (k : ℕ) (hk : k + 267 ≤ Z.s1 T) :
    (∑ a ∈ range 266, orderedBlockGap Z T P hconj k hk a) =
      normalizedSimpleOrdinateAt Z T P hconj ⟨k + 266, by omega⟩ -
        normalizedSimpleOrdinateAt Z T P hconj ⟨k, by omega⟩ := by
  simpa using sum_orderedBlockGap_eq_sub Z T P hconj k hk
    (b := 0) (n := 266) (by omega)

/-- The finite 267-point local bridge, now specialized to the actual
increasing-ordinate simple-zero Gram block and its actual normalized gaps.
The remaining hypothesis is exactly the uniform Gram-to-kernel comparison
for this concrete block. -/
theorem orderedBlock_defect_lower_of_kernel_energy_approx
    (hseven : SevenPointClaim) (hconj : PhiHatConj T P)
    (hL : 0 < P.L T) (k : ℕ) (hk : k + 267 ≤ Z.s1 T)
    (err : ℝ) (herr : 0 ≤ err)
    (happrox :
      blockPairEnergy (orderedBlockGap Z T P hconj k hk) 261 - err ≤
        2 * ZetaSeven.BlockDefect.upperOffDiagEnergy
          (orderedBlockGram Z T P hconj k hk)) :
    261 * ZetaSeven.Assembly.Cstar
        - (∑ j ∈ range 266, orderedBlockGap Z T P hconj k hk j) / 500
        - err
      ≤ spectralDefect
          (orderedBlockGram_posSemidef Z T P hconj k hk) := by
  exact ZetaSeven.BlockEnergyDefect.defect_lower_of_kernel_energy_approx
    hseven (orderedBlockGap Z T P hconj k hk)
      (orderedBlockGap_nonneg Z T P hconj hL k hk)
      (orderedBlockGram_posSemidef Z T P hconj k hk) err herr happrox

end ZetaSeven.ConcreteBlocks
