/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0
-/
import ZetaSeven.SharpCosineKernel
import ZetaSeven.WindowFourierApprox

/-!
# The sharp-window paper Fourier transform

This module supplies the scale conversion missing between the upstream
paper-convention Fourier transform and the normalized sinc kernel used by the
seven-point certificate.
-/

noncomputable section

open Complex MeasureTheory Real Set
open scoped Interval

namespace ZetaSeven.SharpFourierKernel

open Zeta23
open Zeta23.ThmD
open ZetaSeven.ParametricKernel
open ZetaSeven.SharpCosineKernel
open ZetaSeven.WindowFourierApprox

/-- At frequency `2*pi*x/L`, the real part of the sharp-window transform is
`L` times the scale-free sinc numerator. -/
theorem paperFT_sharpW_re_scaled {L : ℝ} (hL : 0 < L) (lam x : ℝ) :
    (paperFT (fun u => (sharpW lam L u : ℂ)) (2 * Real.pi * x / L)).re =
      L * ((Real.sinc ((Real.sqrt 2 * lam - 2 * Real.pi * x) / 2)
        + Real.sinc ((Real.sqrt 2 * lam + 2 * Real.pi * x) / 2)) / 2) := by
  have hint := integrable_ofReal_mul_character
    (integrable_sharpW lam L) (2 * Real.pi * x / L)
  rw [Zeta23.paperFT_def]
  push_cast at hint
  rw [← Zeta23.integral_re_C hint]
  have hreal : ∀ u : ℝ,
      (((sharpW lam L u : ℝ) : ℂ) *
        Complex.exp (I * ((2 * Real.pi * x / L : ℝ) : ℂ) * u)).re =
        sharpW lam L u * Real.cos ((2 * Real.pi * x / L) * u) := by
    intro u
    let y : ℝ := (2 * Real.pi * x / L) * u
    have hy : I * ((2 * Real.pi * x / L : ℝ) : ℂ) * (u : ℂ) =
        (y : ℂ) * I := by
      dsimp [y]
      push_cast
      ring
    rw [hy, Complex.exp_ofReal_mul_I]
    simp only [mul_re, add_re, ofReal_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, add_zero, sub_zero, mul_one]
    simp [y]
  push_cast at hreal
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hreal)]
  have hind :
      (fun u : ℝ => sharpW lam L u * Real.cos ((2 * Real.pi * x / L) * u)) =
        fun u => (Set.Icc (-(L / 2)) (L / 2)).indicator
          (fun u => vStar lam (u / L) *
            Real.cos ((2 * Real.pi * x / L) * u)) u := by
    funext u
    unfold sharpW
    by_cases hu : u ∈ Set.Icc (-(L / 2)) (L / 2) <;> simp [hu]
  rw [hind, MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -(L / 2) ≤ L / 2)]
  have hscale : ∀ u : ℝ,
      vStar lam (u / L) * Real.cos ((2 * Real.pi * x / L) * u) =
        (fun s => vStar lam s * Real.cos (2 * Real.pi * x * s)) (u / L) := by
    intro u
    congr 2
    ring
  rw [intervalIntegral.integral_congr (fun u _ => hscale u),
    intervalIntegral.integral_comp_div
      (f := fun s => vStar lam s * Real.cos (2 * Real.pi * x * s)) hL.ne',
    smul_eq_mul,
    show -(L / 2) / L = (-(1 : ℝ) / 2) by field_simp,
    show (L / 2) / L = ((1 : ℝ) / 2) by field_simp,
    integral_vStar_mul_cos]

/-- Dividing the scaled sharp transform by its mass gives exactly the
parameterized seven-point kernel. -/
theorem paperFT_sharpW_re_normalized {lam L : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (hL : 0 < L) (x : ℝ) :
    (paperFT (fun u => (sharpW lam L u : ℂ)) (2 * Real.pi * x / L)).re /
        (L * aStar lam) = normalizedKernelAt lam x := by
  have ha : aStar lam ≠ 0 := by
    rw [aStar_eq hlam0]
    have hs := sin_theta_pos hlam0 hlam1
    positivity
  rw [paperFT_sharpW_re_scaled hL,
    normalizedKernelAt, sharpMass_eq_aStar hlam0]
  field_simp [hL.ne', ha]

end ZetaSeven.SharpFourierKernel
