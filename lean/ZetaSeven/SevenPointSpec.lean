/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0
-/
/-
# Exact Lean statement of the seven-point computer-assisted target

This module intentionally states, but does not claim to prove, the remaining
transcendental inequality.  The future reflective interval checker must
construct a term of `SevenPointClaim`; keeping the proposition explicit avoids
silently treating an Arb log as a Lean theorem.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import ZetaSeven.Assembly

noncomputable section

namespace ZetaSeven.SevenPointSpec

/-- Normalized Montgomery--Taylor overlap kernel in its entire sinc form. -/
def normalizedKernel (x : ℝ) : ℝ :=
  ((Real.sinc ((Real.sqrt 2 - 2 * Real.pi * x) / 2)
      + Real.sinc ((Real.sqrt 2 + 2 * Real.pi * x) / 2)) / 2) /
    (Real.sqrt 2 * Real.sin (Real.sqrt 2)⁻¹)

/-- Squared normalized overlap. -/
def w (x : ℝ) : ℝ := normalizedKernel x ^ 2

/-- The exact six-gap/seven-point pressure functional. -/
def F6 (g₁ g₂ g₃ g₄ g₅ g₆ : ℝ) : ℝ :=
  (g₁ + g₂ + g₃ + g₄ + g₅ + g₆) / 3000
  + (w g₁ + w g₂ + w g₃ + w g₄ + w g₅ + w g₆) / 3
  + (2 / 5) * (w (g₁ + g₂) + w (g₂ + g₃) + w (g₃ + g₄)
      + w (g₄ + g₅) + w (g₅ + g₆))
  + (1 / 2) * (w (g₁ + g₂ + g₃) + w (g₂ + g₃ + g₄)
      + w (g₃ + g₄ + g₅) + w (g₄ + g₅ + g₆))
  + (2 / 3) * (w (g₁ + g₂ + g₃ + g₄) + w (g₂ + g₃ + g₄ + g₅)
      + w (g₃ + g₄ + g₅ + g₆))
  + w (g₁ + g₂ + g₃ + g₄ + g₅)
  + w (g₂ + g₃ + g₄ + g₅ + g₆)
  + 2 * w (g₁ + g₂ + g₃ + g₄ + g₅ + g₆)

/-- The remaining closed computational proposition.  No theorem in this
artifact assumes this proposition without displaying it as a hypothesis. -/
def SevenPointClaim : Prop :=
  ∀ g₁ g₂ g₃ g₄ g₅ g₆ : ℝ,
    0 ≤ g₁ → 0 ≤ g₂ → 0 ≤ g₃ → 0 ≤ g₄ → 0 ≤ g₅ → 0 ≤ g₆ →
      Assembly.Cstar ≤ F6 g₁ g₂ g₃ g₄ g₅ g₆

end ZetaSeven.SevenPointSpec
