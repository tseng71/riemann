/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import ZetaSeven.ParametricKernel

/-!
# Exact cosine-transform formula for the sharp window

This module proves, including the resonant cases, that the cosine transform
of the scale-free sharp Montgomery--Taylor profile is the sinc expression
used by the parameterized seven-point kernel.
-/

noncomputable section

open Real intervalIntegral
open scoped Interval

namespace ZetaSeven.SharpCosineKernel

open Zeta23.ThmD
open ZetaSeven.ParametricKernel

/-- The symmetric unit-interval cosine integral, written in its entire sinc
form.  Splitting off `c = 0` makes the identity valid at resonance. -/
private theorem integral_cos_mul_unit (c : ℝ) :
    (∫ s in (-(1 : ℝ) / 2)..((1 : ℝ) / 2), Real.cos (c * s)) =
      Real.sinc (c / 2) := by
  by_cases hc : c = 0
  · subst c
    norm_num [intervalIntegral.integral_const]
  · rw [intervalIntegral.integral_comp_mul_left Real.cos hc,
      integral_cos, smul_eq_mul]
    rw [show c * (-(1 : ℝ) / 2) = -(c / 2) by ring,
      show c * ((1 : ℝ) / 2) = c / 2 by ring, Real.sin_neg,
      Real.sinc_of_ne_zero (div_ne_zero hc (by norm_num))]
    field_simp
    ring

/-- Product-to-sum, integrated on the symmetric unit interval. -/
theorem integral_cos_mul_cos_unit (a b : ℝ) :
    (∫ s in (-(1 : ℝ) / 2)..((1 : ℝ) / 2),
        Real.cos (a * s) * Real.cos (b * s)) =
      (Real.sinc ((a - b) / 2) + Real.sinc ((a + b) / 2)) / 2 := by
  have hpoint : ∀ s : ℝ,
      Real.cos (a * s) * Real.cos (b * s) =
        (1 / 2 : ℝ) * Real.cos ((a - b) * s) +
          (1 / 2 : ℝ) * Real.cos ((a + b) * s) := by
    intro s
    rw [show (a - b) * s = a * s - b * s by ring,
      show (a + b) * s = a * s + b * s by ring,
      Real.cos_sub, Real.cos_add]
    ring
  rw [intervalIntegral.integral_congr (fun s _ => hpoint s)]
  rw [intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_cos_mul_unit, integral_cos_mul_unit]
  ring

/-- Exact sinc formula for the sharp profile's cosine transform. -/
theorem integral_vStar_mul_cos (lam x : ℝ) :
    (∫ s in (-(1 : ℝ) / 2)..((1 : ℝ) / 2),
        vStar lam s * Real.cos (2 * Real.pi * x * s)) =
      (Real.sinc ((Real.sqrt 2 * lam - 2 * Real.pi * x) / 2)
        + Real.sinc ((Real.sqrt 2 * lam + 2 * Real.pi * x) / 2)) / 2 := by
  simpa [vStar] using
    (integral_cos_mul_cos_unit (Real.sqrt 2 * lam) (2 * Real.pi * x))

/-- After normalization by the sharp mass, the exact cosine transform is the
parameterized kernel. -/
theorem normalized_integral_eq_kernel {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    (∫ s in (-(1 : ℝ) / 2)..((1 : ℝ) / 2),
        vStar lam s * Real.cos (2 * Real.pi * x * s)) / aStar lam =
      normalizedKernelAt lam x := by
  rw [integral_vStar_mul_cos, normalizedKernelAt,
    sharpMass_eq_aStar hlam]

/-- The endpoint transform is exactly the kernel used by the seven-point
certificate. -/
theorem normalized_integral_one_eq_certificate (x : ℝ) :
    (∫ s in (-(1 : ℝ) / 2)..((1 : ℝ) / 2),
        vStar 1 s * Real.cos (2 * Real.pi * x * s)) / aStar 1 =
      ZetaSeven.SevenPointSpec.normalizedKernel x := by
  rw [normalized_integral_eq_kernel one_pos,
    normalizedKernelAt_one]

end ZetaSeven.SharpCosineKernel
