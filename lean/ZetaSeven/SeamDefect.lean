/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.Assembly.SeamMult
import ZetaSeven.SimpleBlock

/-!
# Tail seam with the simple-zero spectral defect retained

This is the defect-preserving analogue of upstream `seamA_mult2`.  It carries
the exact simple-zero Gram defect through the perturbation from the finite
zero matrix `A` to the full Gram matrix `G`, and through the passage from the
expanded interval `I'` to `(T, 2T]`.
-/

noncomputable section

open RHLinalg
open ZetaSeven.Stability
open scoped ComplexOrder BigOperators

namespace ZetaSeven.SeamDefect

open Zeta23
open Zeta23.Assembly
open Zeta23.ZeroSide

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

/-- Seam A with the simple-zero Gram defect left on the favorable side. -/
theorem seamA_simple_defect (hT : 0 ≤ T) (hconj : PhiHatConj T P)
    (hreal : PhiHatReal T P) (hPois : PoissonSq T P)
    {θ₀ : ℝ} (hTl : TailInputs Z P T θ₀) (ha : 0 < P.a T)
    (hL : 0 < P.L T) :
    4 * rtrace (P.hat T (Z.Gz P T))
        - frobSq (P.hat T (Z.Gz P T))
        - 2 * (Z.N T (2 * T) : ℝ)
        - 3 * (NII Z T : ℝ)
        - θ₀ / (P.a T * P.L T)
          * (4 + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T)))
            + θ₀ / (P.a T * P.L T))
        + spectralDefect
          (Matrix.posSemidef_conjTranspose_mul_self
            (ZetaSeven.SimpleBlock.zetaSimpleW Z T P hconj))
      ≤ Z.N0s T (2 * T) := by
  obtain ⟨Bc, hB0, htrE, hfrE, hBle⟩ := hTl.hat
  have hGAE : P.hat T (Z.Gz P T)
      = P.hat T (Z.Az P T) + P.hat T (Z.Ez P T) := by
    rw [← hat_add]
    congr 1
    simp [ZeroConfig.Ez]
  have hB₀ : 0 ≤ θ₀ / (P.a T * P.L T) :=
    div_nonneg hTl.theta_nonneg (mul_pos ha hL).le
  have hcore := ZetaSeven.SimpleBlock.hatAz_simple_defect
    Z T P hconj hreal hPois (by positivity)
  have hpert := ctr_sub_frobSq_perturb 4 (by norm_num) hGAE hB₀
    (htrE.trans hBle) (hfrE.trans (pow_le_pow_left₀ hB0 hBle 2))
  have hs1 : (Z.s1 T : ℝ)
      ≤ (Z.N0s T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast s1_le Z hT
  have hNI : (Z.NIprime T : ℝ)
      = (Z.N T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast NIprime_eq Z hT
  rw [hNI] at hcore
  linarith [hcore, hpert, hs1]

end ZetaSeven.SeamDefect
