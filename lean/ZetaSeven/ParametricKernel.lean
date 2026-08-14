/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ThmD.Functional
import ZetaSeven.SevenPointSpec

/-!
# The lambda-dependent seven-point kernel

The sharp Montgomery--Taylor window occurring in the fixed-`lambda`
Theorem-D argument has profile `cos (sqrt 2 * lambda * s)`.  The existing
computer-assisted seven-point specification is its endpoint `lambda = 1`.
This module records the parameterized kernel and proves that its endpoint is
definitionally the kernel used by the certificate.  Keeping the parameter
visible prevents an invalid substitution of the endpoint kernel into an
argument whose analytic estimates require `lambda < 1`.
-/

noncomputable section

namespace ZetaSeven.ParametricKernel

open Zeta23.ThmD

/-- The mass of the sharp cosine window on `[-1/2, 1/2]`, in closed form. -/
def sharpMass (lam : ℝ) : ℝ :=
  Real.sqrt 2 * Real.sin (theta lam) / lam

/-- The parameterized normalized Fourier kernel of the sharp cosine window. -/
def normalizedKernelAt (lam x : ℝ) : ℝ :=
  ((Real.sinc ((Real.sqrt 2 * lam - 2 * Real.pi * x) / 2)
      + Real.sinc ((Real.sqrt 2 * lam + 2 * Real.pi * x) / 2)) / 2) /
    sharpMass lam

/-- The closed-form mass agrees with the integral `aStar` away from the
singular parameter `lambda = 0`. -/
theorem sharpMass_eq_aStar {lam : ℝ} (hlam : 0 < lam) :
    sharpMass lam = aStar lam := by
  unfold sharpMass
  exact (aStar_eq hlam).symm

/-- At `lambda = 1` the parameterized kernel is exactly the kernel appearing
in the seven-point certificate. -/
theorem normalizedKernelAt_one (x : ℝ) :
    normalizedKernelAt 1 x = ZetaSeven.SevenPointSpec.normalizedKernel x := by
  simp [normalizedKernelAt, sharpMass, ZetaSeven.SevenPointSpec.normalizedKernel,
    theta_one]

/-- Squared parameterized kernel. -/
def wAt (lam x : ℝ) : ℝ := normalizedKernelAt lam x ^ 2

theorem wAt_one (x : ℝ) :
    wAt 1 x = ZetaSeven.SevenPointSpec.w x := by
  simp [wAt, ZetaSeven.SevenPointSpec.w, normalizedKernelAt_one]

/-- The six-gap pressure functional with the analytic parameter left
explicit. -/
def F6At (lam g₁ g₂ g₃ g₄ g₅ g₆ : ℝ) : ℝ :=
  (g₁ + g₂ + g₃ + g₄ + g₅ + g₆) / 3000
  + (wAt lam g₁ + wAt lam g₂ + wAt lam g₃ + wAt lam g₄
      + wAt lam g₅ + wAt lam g₆) / 3
  + (2 / 5) * (wAt lam (g₁ + g₂) + wAt lam (g₂ + g₃)
      + wAt lam (g₃ + g₄) + wAt lam (g₄ + g₅)
      + wAt lam (g₅ + g₆))
  + (1 / 2) * (wAt lam (g₁ + g₂ + g₃)
      + wAt lam (g₂ + g₃ + g₄) + wAt lam (g₃ + g₄ + g₅)
      + wAt lam (g₄ + g₅ + g₆))
  + (2 / 3) * (wAt lam (g₁ + g₂ + g₃ + g₄)
      + wAt lam (g₂ + g₃ + g₄ + g₅)
      + wAt lam (g₃ + g₄ + g₅ + g₆))
  + wAt lam (g₁ + g₂ + g₃ + g₄ + g₅)
  + wAt lam (g₂ + g₃ + g₄ + g₅ + g₆)
  + 2 * wAt lam (g₁ + g₂ + g₃ + g₄ + g₅ + g₆)

/-- The endpoint parameterized functional is exactly the existing
seven-point functional. -/
theorem F6At_one (g₁ g₂ g₃ g₄ g₅ g₆ : ℝ) :
    F6At 1 g₁ g₂ g₃ g₄ g₅ g₆ =
      ZetaSeven.SevenPointSpec.F6 g₁ g₂ g₃ g₄ g₅ g₆ := by
  simp [F6At, ZetaSeven.SevenPointSpec.F6, wAt_one]

end ZetaSeven.ParametricKernel
