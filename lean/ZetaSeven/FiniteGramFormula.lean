/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0
-/
import ZetaSeven.OrderedSimpleZeros

/-!
# Exact entries of the finite ordered simple-zero Gram matrix

This module opens the analytic Gram-to-kernel interface at the level of
individual entries.  It proves that the columns used by the finite
zero-side argument are exactly the normalized Fourier samples at the
increasingly ordered simple zeros.  No limiting or kernel approximation is
used here.
-/

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset
open scoped ComplexOrder BigOperators

namespace ZetaSeven.FiniteGramFormula

open Zeta23
open Zeta23.ZeroSide
open Zeta23.ZeroSide.RankTraceMult
open ZetaSeven.OrderedSimpleZeros

variable (Z : ZeroConfig) (T : ℝ) (P : Params)

/-- Every member of the increasing simple-zero enumeration is on the
critical line. -/
theorem simpleZeroAt_re_eq_half (hconj : PhiHatConj T P)
    (i : Fin (Z.s1 T)) :
    (simpleZeroAt Z T P hconj i).re = 1 / 2 := by
  have hz := (simpleBlockEquiv Z T P hconj i).2
  simp only [ZeroBlockData.S₁, Finset.mem_filter, Finset.mem_univ,
    true_and] at hz
  exact
    (mkData_σ_eq_iff Z T (evalVec Z T P) (evalVec_reflect hconj)
      (simpleBlockEquiv Z T P hconj i)).mp hz.1

/-- Hence the spectral ordinate `gammaOf` of an ordered simple zero is its
physical (real) ordinate. -/
theorem gammaOf_simpleZeroAt (hconj : PhiHatConj T P)
    (i : Fin (Z.s1 T)) :
    gammaOf (simpleZeroAt Z T P hconj i) =
      (simpleOrdinateAt Z T P hconj i : ℂ) := by
  simpa [simpleOrdinateAt] using
    (gammaOf_of_re_eq_half
      (simpleZeroAt_re_eq_half Z T P hconj i))

/-- Exact entry formula for the normalized finite column matrix. -/
theorem orderedSimpleW_apply (hconj : PhiHatConj T P)
    (k : Fin (P.d T)) (i : Fin (Z.s1 T)) :
    orderedSimpleW Z T P hconj k i =
      P.phiHat T
          ((simpleOrdinateAt Z T P hconj i : ℂ) - P.tau T k) /
        (Real.sqrt (P.a T * P.L T ^ 2) : ℂ) := by
  change
    P.phiHat T
          (gammaOf (simpleZeroAt Z T P hconj i) - P.tau T k) /
        (Real.sqrt (P.a T * P.L T ^ 2) : ℂ) = _
  rw [gammaOf_simpleZeroAt Z T P hconj i]

/-- The finite ordered Gram entry is the exact finite grid inner product of
the normalized Fourier samples.  This identity is the starting point for
separating the full Poisson sum from the two missing endpoint tails. -/
theorem orderedSimpleGram_apply (hconj : PhiHatConj T P)
    (i j : Fin (Z.s1 T)) :
    orderedSimpleGram Z T P hconj i j =
      ∑ k : Fin (P.d T),
        star
            (P.phiHat T
                ((simpleOrdinateAt Z T P hconj i : ℂ) - P.tau T k) /
              (Real.sqrt (P.a T * P.L T ^ 2) : ℂ)) *
          (P.phiHat T
              ((simpleOrdinateAt Z T P hconj j : ℂ) - P.tau T k) /
            (Real.sqrt (P.a T * P.L T ^ 2) : ℂ)) := by
  rw [orderedSimpleGram_eq_mul]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    orderedSimpleW_apply Z T P hconj]

end ZetaSeven.FiniteGramFormula
