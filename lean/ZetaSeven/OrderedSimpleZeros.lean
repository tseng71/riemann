/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0
-/
import ZetaSeven.Pinching
import ZetaSeven.SimpleBlock
import Mathlib.Data.Fintype.Sort

/-!
# Increasing-ordinate coordinates for the concrete simple-zero Gram matrix

The simple critical-line columns produced by `ZetaSeven.SimpleBlock` are
indexed by a finite subtype with no chosen order.  This module proves that
the ordinate is injective on that subtype, enumerates it increasingly by
`Fin (Z.s1 T)`, and reindexes the concrete Gram matrix along that exact
equivalence.  The reindexing preserves the full spectral defect.

No local kernel approximation or endpoint deletion is used here.  Those
remain separate analytic inputs.
-/

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset
open scoped ComplexOrder BigOperators

namespace ZetaSeven.OrderedSimpleZeros

open Zeta23
open Zeta23.ZeroSide
open ZetaSeven.Stability
open ZetaSeven.Pinching

variable (Z : ZeroConfig) (T : ℝ) (P : Params)

/- A wrapper avoids inheriting the unrelated partial order on `ℂ`; its
linear order below is lifted solely from the ordinate. -/
private structure SimpleIndex (hconj : PhiHatConj T P) where
  val : (blockData Z T P hconj).S₁

private def simpleIndexEquivBlock (hconj : PhiHatConj T P) :
    SimpleIndex Z T P hconj ≃ (blockData Z T P hconj).S₁ where
  toFun z := z.val
  invFun z := ⟨z⟩
  left_inv z := by cases z; rfl
  right_inv _ := rfl

private noncomputable instance simpleIndexFintype
    (hconj : PhiHatConj T P) : Fintype (SimpleIndex Z T P hconj) :=
  Fintype.ofEquiv (blockData Z T P hconj).S₁
    (simpleIndexEquivBlock Z T P hconj).symm

private instance simpleIndexDecidableEq (hconj : PhiHatConj T P) :
    DecidableEq (SimpleIndex Z T P hconj) :=
  (simpleIndexEquivBlock Z T P hconj).decidableEq

private def simpleOrdinate (hconj : PhiHatConj T P)
    (z : SimpleIndex Z T P hconj) : ℝ :=
  ((z.val : ZI Z T) : ℂ).im

/-- Two concrete simple critical-line zeros with the same ordinate are the
same zero. -/
private lemma simpleOrdinate_injective (hconj : PhiHatConj T P) :
    Function.Injective (simpleOrdinate Z T P hconj) := by
  intro z z' him
  rcases z with ⟨z⟩
  rcases z' with ⟨z'⟩
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  apply Complex.ext
  · have hz := z.2
    have hz' := z'.2
    simp only [ZeroBlockData.S₁, Finset.mem_filter, Finset.mem_univ,
      true_and] at hz hz'
    have hzre : ((z : ZI Z T) : ℂ).re = 1 / 2 := by
      exact (mkData_σ_eq_iff Z T _ (evalVec_reflect hconj) z).mp hz.1
    have hzre' : ((z' : ZI Z T) : ℂ).re = 1 / 2 := by
      exact (mkData_σ_eq_iff Z T _ (evalVec_reflect hconj) z').mp hz'.1
    exact hzre.trans hzre'.symm
  · exact him

private structure SimpleOrdering (hconj : PhiHatConj T P) where
  equiv : Fin (Z.s1 T) ≃ SimpleIndex Z T P hconj
  ordinate_strictMono :
    StrictMono (fun i => simpleOrdinate Z T P hconj (equiv i))

/-- Canonical increasing-ordinate enumeration of the concrete simple-zero
subtype used by the zero-side Gram matrix. -/
private def simpleOrdering (hconj : PhiHatConj T P) :
    SimpleOrdering Z T P hconj := by
  letI : LinearOrder (SimpleIndex Z T P hconj) :=
    LinearOrder.lift' (simpleOrdinate Z T P hconj)
      (simpleOrdinate_injective Z T P hconj)
  have hcard :
      Fintype.card (SimpleIndex Z T P hconj) = Z.s1 T := by
    have hs := s1_eq_mk Z T (evalVec Z T P) (evalVec_reflect hconj)
    calc
      Fintype.card (SimpleIndex Z T P hconj) =
          Fintype.card (blockData Z T P hconj).S₁ :=
        Fintype.card_congr (simpleIndexEquivBlock Z T P hconj)
      _ = #(blockData Z T P hconj).S₁ := Fintype.card_coe _
      _ = Z.s1 T := by
        simpa only [ZeroBlockData.s₁, blockData] using hs.symm
  let eord : Fin (Z.s1 T) ≃o SimpleIndex Z T P hconj :=
    Fintype.orderIsoFinOfCardEq (SimpleIndex Z T P hconj) hcard
  refine ⟨eord.toEquiv, ?_⟩
  intro i j hij
  exact eord.lt_iff_lt.mpr hij

/-- Equivalence from increasing positions to the concrete column subtype of
the simple-zero Gram matrix. -/
def simpleBlockEquiv (hconj : PhiHatConj T P) :
    Fin (Z.s1 T) ≃ (blockData Z T P hconj).S₁ :=
  (simpleOrdering Z T P hconj).equiv.trans
    (simpleIndexEquivBlock Z T P hconj)

/-- The concrete simple zero at increasing-ordinate position `i`. -/
def simpleZeroAt (hconj : PhiHatConj T P) (i : Fin (Z.s1 T)) : ℂ :=
  ((simpleBlockEquiv Z T P hconj i : ZI Z T) : ℂ)

/-- The physical ordinate of the concrete simple zero at position `i`. -/
def simpleOrdinateAt (hconj : PhiHatConj T P)
    (i : Fin (Z.s1 T)) : ℝ :=
  (simpleZeroAt Z T P hconj i).im

lemma simpleOrdinateAt_strictMono (hconj : PhiHatConj T P) :
    StrictMono (simpleOrdinateAt Z T P hconj) := by
  intro i j hij
  simpa [simpleOrdinateAt, simpleZeroAt, simpleBlockEquiv,
    simpleIndexEquivBlock, simpleOrdinate] using
      (simpleOrdering Z T P hconj).ordinate_strictMono hij

/-- The normalized coordinate `L(γ-T)/(2π)` used by the local overlap
kernel. -/
def normalizedSimpleOrdinateAt (hconj : PhiHatConj T P)
    (i : Fin (Z.s1 T)) : ℝ :=
  P.L T * (simpleOrdinateAt Z T P hconj i - T) / (2 * Real.pi)

lemma normalizedSimpleOrdinateAt_strictMono
    (hconj : PhiHatConj T P) (hL : 0 < P.L T) :
    StrictMono (normalizedSimpleOrdinateAt Z T P hconj) := by
  intro i j hij
  have hγ := simpleOrdinateAt_strictMono Z T P hconj hij
  unfold normalizedSimpleOrdinateAt
  have hden : 0 < 2 * Real.pi := by positivity
  apply (div_lt_div_iff_of_pos_right hden).2
  exact mul_lt_mul_of_pos_left (sub_lt_sub_right hγ T) hL

/-- Consecutive normalized gap in the increasing simple-zero list. -/
def simpleGap (hconj : PhiHatConj T P) (i : Fin (Z.s1 T - 1)) : ℝ :=
  normalizedSimpleOrdinateAt Z T P hconj ⟨i + 1, by omega⟩ -
    normalizedSimpleOrdinateAt Z T P hconj ⟨i, by omega⟩

lemma simpleGap_pos (hconj : PhiHatConj T P) (hL : 0 < P.L T)
    (i : Fin (Z.s1 T - 1)) : 0 < simpleGap Z T P hconj i := by
  unfold simpleGap
  exact sub_pos.mpr
    ((normalizedSimpleOrdinateAt_strictMono Z T P hconj hL) (by simp))

lemma simpleGap_nonneg (hconj : PhiHatConj T P) (hL : 0 < P.L T)
    (i : Fin (Z.s1 T - 1)) : 0 ≤ simpleGap Z T P hconj i :=
  (simpleGap_pos Z T P hconj hL i).le

/-- The concrete simple-zero column matrix, with columns reindexed by
increasing ordinate. -/
def orderedSimpleW (hconj : PhiHatConj T P) :
    Matrix (Fin (P.d T)) (Fin (Z.s1 T)) ℂ :=
  Matrix.reindex (Equiv.refl _) (simpleBlockEquiv Z T P hconj).symm
    (ZetaSeven.SimpleBlock.zetaSimpleW Z T P hconj)

/-- The concrete simple-zero Gram matrix on the increasing index `Fin s₁`. -/
def orderedSimpleGram (hconj : PhiHatConj T P) :
    Matrix (Fin (Z.s1 T)) (Fin (Z.s1 T)) ℂ :=
  Matrix.reindex (simpleBlockEquiv Z T P hconj).symm
    (simpleBlockEquiv Z T P hconj).symm
      ((ZetaSeven.SimpleBlock.zetaSimpleW Z T P hconj)ᴴ *
        ZetaSeven.SimpleBlock.zetaSimpleW Z T P hconj)

theorem orderedSimpleGram_eq_mul (hconj : PhiHatConj T P) :
    orderedSimpleGram Z T P hconj =
      (orderedSimpleW Z T P hconj)ᴴ * orderedSimpleW Z T P hconj := by
  ext i j
  simp only [orderedSimpleGram, orderedSimpleW, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Equiv.symm_symm, Equiv.refl_symm, Equiv.coe_refl, id_eq]

/-- Positivity of the increasing-index concrete simple-zero Gram matrix. -/
theorem orderedSimpleGram_posSemidef (hconj : PhiHatConj T P) :
    (orderedSimpleGram Z T P hconj).PosSemidef :=
  ZetaSeven.Pinching.posSemidefReindex
    (Matrix.posSemidef_conjTranspose_mul_self
      (ZetaSeven.SimpleBlock.zetaSimpleW Z T P hconj))
    (simpleBlockEquiv Z T P hconj).symm

/-- Reindexing the actual simple-zero Gram matrix by increasing ordinate
preserves the full spectral defect exactly. -/
theorem orderedSimpleGram_spectralDefect (hconj : PhiHatConj T P) :
    spectralDefect (orderedSimpleGram_posSemidef Z T P hconj) =
      spectralDefect
        (Matrix.posSemidef_conjTranspose_mul_self
          (ZetaSeven.SimpleBlock.zetaSimpleW Z T P hconj)) :=
  ZetaSeven.Pinching.spectralDefect_reindex
    (Matrix.posSemidef_conjTranspose_mul_self
      (ZetaSeven.SimpleBlock.zetaSimpleW Z T P hconj))
    (simpleBlockEquiv Z T P hconj).symm

end ZetaSeven.OrderedSimpleZeros
