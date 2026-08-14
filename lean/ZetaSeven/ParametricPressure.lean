/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0
-/
import ZetaSeven.KernelBounds

/-!
# Uniform lambda-stability of the seven-point pressure

The total positive weight of the 21 kernel-square terms in `F6At` is `12`.
Combining this with the uniform `4 * |lambda-mu|` bound for each squared
kernel gives the explicit global constant `48`.
-/

noncomputable section

namespace ZetaSeven.ParametricPressure

open ZetaSeven.ParametricKernel
open ZetaSeven.KernelBounds

/-- Uniform stability of the complete six-gap pressure functional. -/
set_option maxHeartbeats 1000000 in
theorem abs_F6At_sub_le_48 {lam mu : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hmu0 : 0 < mu) (hmu1 : mu ≤ 1)
    (g₁ g₂ g₃ g₄ g₅ g₆ : ℝ) :
    |F6At lam g₁ g₂ g₃ g₄ g₅ g₆ -
        F6At mu g₁ g₂ g₃ g₄ g₅ g₆| ≤ 48 * |lam - mu| := by
  have hw (y : ℝ) : |wAt lam y - wAt mu y| ≤ 4 * |lam - mu| :=
    abs_wAt_sub_le_four hlam0 hlam1 hmu0 hmu1 y
  rcases abs_le.mp (hw g₁) with ⟨h1l, h1u⟩
  rcases abs_le.mp (hw g₂) with ⟨h2l, h2u⟩
  rcases abs_le.mp (hw g₃) with ⟨h3l, h3u⟩
  rcases abs_le.mp (hw g₄) with ⟨h4l, h4u⟩
  rcases abs_le.mp (hw g₅) with ⟨h5l, h5u⟩
  rcases abs_le.mp (hw g₆) with ⟨h6l, h6u⟩
  rcases abs_le.mp (hw (g₁ + g₂)) with ⟨h12l, h12u⟩
  rcases abs_le.mp (hw (g₂ + g₃)) with ⟨h23l, h23u⟩
  rcases abs_le.mp (hw (g₃ + g₄)) with ⟨h34l, h34u⟩
  rcases abs_le.mp (hw (g₄ + g₅)) with ⟨h45l, h45u⟩
  rcases abs_le.mp (hw (g₅ + g₆)) with ⟨h56l, h56u⟩
  rcases abs_le.mp (hw (g₁ + g₂ + g₃)) with ⟨h123l, h123u⟩
  rcases abs_le.mp (hw (g₂ + g₃ + g₄)) with ⟨h234l, h234u⟩
  rcases abs_le.mp (hw (g₃ + g₄ + g₅)) with ⟨h345l, h345u⟩
  rcases abs_le.mp (hw (g₄ + g₅ + g₆)) with ⟨h456l, h456u⟩
  rcases abs_le.mp (hw (g₁ + g₂ + g₃ + g₄)) with ⟨h1234l, h1234u⟩
  rcases abs_le.mp (hw (g₂ + g₃ + g₄ + g₅)) with ⟨h2345l, h2345u⟩
  rcases abs_le.mp (hw (g₃ + g₄ + g₅ + g₆)) with ⟨h3456l, h3456u⟩
  rcases abs_le.mp (hw (g₁ + g₂ + g₃ + g₄ + g₅)) with ⟨h12345l, h12345u⟩
  rcases abs_le.mp (hw (g₂ + g₃ + g₄ + g₅ + g₆)) with ⟨h23456l, h23456u⟩
  rcases abs_le.mp (hw (g₁ + g₂ + g₃ + g₄ + g₅ + g₆)) with ⟨h123456l, h123456u⟩
  have hd : 0 ≤ |lam - mu| := abs_nonneg _
  rw [abs_le]
  constructor <;> unfold F6At <;> nlinarith

/-- An endpoint seven-point certificate transfers to every fixed
`0 < lambda <= 1`, with an explicit loss tending to zero as `lambda -> 1`. -/
theorem endpointClaim_implies_parametric
    (hclaim : ZetaSeven.SevenPointSpec.SevenPointClaim)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    ∀ g₁ g₂ g₃ g₄ g₅ g₆ : ℝ,
      0 ≤ g₁ → 0 ≤ g₂ → 0 ≤ g₃ → 0 ≤ g₄ → 0 ≤ g₅ → 0 ≤ g₆ →
        ZetaSeven.Assembly.Cstar - 48 * |lam - 1| ≤
          F6At lam g₁ g₂ g₃ g₄ g₅ g₆ := by
  intro g₁ g₂ g₃ g₄ g₅ g₆ hg₁ hg₂ hg₃ hg₄ hg₅ hg₆
  have hbase := hclaim g₁ g₂ g₃ g₄ g₅ g₆ hg₁ hg₂ hg₃ hg₄ hg₅ hg₆
  have hstable := abs_F6At_sub_le_48
    hlam0 hlam1 one_pos le_rfl g₁ g₂ g₃ g₄ g₅ g₆
  have hlower := (abs_le.mp hstable).1
  rw [F6At_one] at hlower
  linarith

end ZetaSeven.ParametricPressure
