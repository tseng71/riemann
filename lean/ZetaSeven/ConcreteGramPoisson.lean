/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ThmD.ZeroSideD
import ZetaSeven.FiniteGramFormula
import ZetaSeven.FinitePoissonDecomposition

/-!
# Concrete smooth-window Gram entries

This module specializes the exact ordered simple-zero Gram formula to the
window-realizing parameter family `P.atD T`.  The result is written entirely
with the real Fourier transform of the smooth Montgomery--Taylor window and
the explicit arithmetic grid.  It is the finite side of the subsequent
Poisson retained/tail decomposition.
-/

noncomputable section

open Matrix Finset
open scoped ComplexOrder BigOperators

namespace ZetaSeven.ConcreteGramPoisson

open Zeta23
open Zeta23.ZeroSide
open Zeta23.ThmD
open ZetaSeven.OrderedSimpleZeros
open ZetaSeven.FinitePoissonDecomposition

/-- Canonical conjugation witness for the window-realizing parameters. -/
def atDConj (P : Params) (T : ℝ) : PhiHatConj T (P.atD T) :=
  fun z => GzGp.phiHat_conj (P.atD T) T z

/-- Canonical real-axis witness for the window-realizing parameters. -/
def atDReal (P : Params) (T : ℝ) : PhiHatReal T (P.atD T) :=
  fun r => GzGp.phiHat_ofReal (P.atD T) T r

/-- Exact concrete entry formula: the ordered Gram matrix for `P.atD T` is
the finite correlation of the real smooth-window Fourier samples on the
explicit grid `T + k * (2*pi/L)`. -/
theorem orderedSimpleGram_atD_apply
    (Z : ZeroConfig) (P : Params) (hP : P.Valid) (T : ℝ)
    (i j : Fin (Z.s1 T)) :
    orderedSimpleGram Z T (P.atD T) (atDConj P T) i j =
      ∑ k : Fin (P.d T),
        ((AdmWindow.vHatR (P.phiD T)
              (simpleOrdinateAt Z T (P.atD T) (atDConj P T) i -
                (T + (k : ℤ) * (2 * Real.pi / P.L T))) : ℂ) /
            (Real.sqrt
              (AdmWindow.av (P.phiD T) (P.L T) * P.L T ^ 2) : ℂ)) *
          ((AdmWindow.vHatR (P.phiD T)
              (simpleOrdinateAt Z T (P.atD T) (atDConj P T) j -
                (T + (k : ℤ) * (2 * Real.pi / P.L T))) : ℂ) /
            (Real.sqrt
              (AdmWindow.av (P.phiD T) (P.L T) * P.L T ^ 2) : ℂ)) := by
  rw [ZetaSeven.FiniteGramFormula.orderedSimpleGram_apply_real_samples
    Z T (P.atD T) (atDConj P T) (atDReal P T)]
  simp only [Params.atD_d, atD_phiHatR hP T, atD_tau_eq,
    Params.atD_L, atD_a_eq_av hP T]

/-- After the positive normalization is collected, the same entry is the
finite `gridCorrelation` sum divided by the exact window mass. -/
theorem orderedSimpleGram_atD_apply_gridCorrelation
    (Z : ZeroConfig) (P : Params) (hP : P.Valid) (T : ℝ)
    (hq : 0 < AdmWindow.av (P.phiD T) (P.L T) * P.L T ^ 2)
    (i j : Fin (Z.s1 T)) :
    orderedSimpleGram Z T (P.atD T) (atDConj P T) i j =
      ∑ k : Fin (P.d T),
        ((gridCorrelation (P.phiD T) (P.L T) T
              (simpleOrdinateAt Z T (P.atD T) (atDConj P T) i)
              (simpleOrdinateAt Z T (P.atD T) (atDConj P T) j)
              (k : ℤ) /
            (AdmWindow.av (P.phiD T) (P.L T) * P.L T ^ 2) : ℝ) : ℂ) := by
  rw [orderedSimpleGram_atD_apply Z P hP T]
  apply Finset.sum_congr rfl
  intro k _
  unfold gridCorrelation
  have hs :
      (Real.sqrt
          (AdmWindow.av (P.phiD T) (P.L T) * P.L T ^ 2) : ℂ) *
          (Real.sqrt
            (AdmWindow.av (P.phiD T) (P.L T) * P.L T ^ 2) : ℂ) =
        (AdmWindow.av (P.phiD T) (P.L T) * P.L T ^ 2 : ℝ) := by
    push_cast
    nlinarith [Real.sq_sqrt hq.le]
  push_cast
  rw [div_mul_div_comm, hs]

/-- Retained-sum form of the concrete entry.  Combining this theorem with
`retained_eq_full_sub_omitted` isolates the endpoint tails in one rewrite. -/
theorem orderedSimpleGram_atD_apply_retained
    (Z : ZeroConfig) (P : Params) (hP : P.Valid) (T : ℝ)
    (hq : 0 < AdmWindow.av (P.phiD T) (P.L T) * P.L T ^ 2)
    (i j : Fin (Z.s1 T)) :
    orderedSimpleGram Z T (P.atD T) (atDConj P T) i j =
      ((retainedCorrelation (P.phiD T) (P.L T) T
            (simpleOrdinateAt Z T (P.atD T) (atDConj P T) i)
            (simpleOrdinateAt Z T (P.atD T) (atDConj P T) j)
            (P.d T) /
          (AdmWindow.av (P.phiD T) (P.L T) * P.L T ^ 2) : ℝ) : ℂ) := by
  rw [orderedSimpleGram_atD_apply_gridCorrelation Z P hP T hq]
  rw [retainedCorrelation_eq_fin]
  push_cast
  rw [Finset.sum_div]

/-- Full Poisson-kernel minus endpoint-tail formula for a concrete ordered
simple-zero Gram entry.  No asymptotic estimate is used: the only remaining
analytic task is to bound the explicitly displayed omitted correlation. -/
theorem orderedSimpleGram_atD_apply_full_sub_omitted
    (Z : ZeroConfig) (P : Params) (hP : P.Valid) (T : ℝ)
    (h8 : 8 * P.w ≤ P.L T)
    (hq : 0 < AdmWindow.av (P.phiD T) (P.L T) * P.L T ^ 2)
    (i j : Fin (Z.s1 T)) :
    orderedSimpleGram Z T (P.atD T) (atDConj P T) i j =
      (((P.L T * AdmWindow.VPhiR (P.phiD T)
              (simpleOrdinateAt Z T (P.atD T) (atDConj P T) i -
                simpleOrdinateAt Z T (P.atD T) (atDConj P T) j) -
            omittedCorrelation (P.phiD T) (P.L T) T
              (simpleOrdinateAt Z T (P.atD T) (atDConj P T) i)
              (simpleOrdinateAt Z T (P.atD T) (atDConj P T) j)
              (P.d T)) /
          (AdmWindow.av (P.phiD T) (P.L T) * P.L T ^ 2) : ℝ) : ℂ) := by
  rw [orderedSimpleGram_atD_apply_retained Z P hP T hq]
  rw [retained_eq_full_sub_omitted (admWindow_params hP h8)]

end ZetaSeven.ConcreteGramPoisson
