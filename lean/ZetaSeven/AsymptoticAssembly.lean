/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.Assembly
import ZetaSeven.Assembly

/-!
# Asymptotic assembly of the seven-point stability gain

This module turns the finite algebra in `ZetaSeven.Assembly` into the usual
epsilon-form proportion statement.  It deliberately takes the analytic
source inequality and the local seven-point defect estimate as hypotheses.
Thus any future proof of the local estimate can be plugged into this theorem
without changing the endgame.
-/

noncomputable section

open Filter Asymptotics Topology

namespace ZetaSeven.AsymptoticAssembly

open Zeta23.Assembly

/-- If the defect-preserving source inequality and the local seven-point
defect bound hold eventually, and both displayed errors are `o(N)`, then the
assembled coefficient holds in epsilon form. -/
theorem assemble_stability_eps
    {H C : ℝ} {N S D errorSource errorLocal : ℝ → ℝ}
    (hden : 0 < 267 - 261 * C)
    (hsource : ∀ᶠ T in atTop,
      H * N T + D T - errorSource T ≤ S T)
    (hlocal : ∀ᶠ T in atTop,
      (261 * C / 267) * S T - (266 / 133500) * N T
        - errorLocal T ≤ D T)
    (hN : ∀ᶠ T in atTop, 0 ≤ N T)
    (hSourceError : errorSource =o[atTop] N)
    (hLocalError : errorLocal =o[atTop] N) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((267 * H - 266 / 500) / (267 - 261 * C) - ε) * N T ≤ S T := by
  let error : ℝ → ℝ := fun T =>
    267 * (errorSource T + errorLocal T) / (267 - 261 * C)
  have hmain : ∀ᶠ T in atTop,
      ((267 * H - 266 / 500) / (267 - 261 * C)) * N T
        - error T ≤ S T := by
    filter_upwards [hsource, hlocal] with T hs hl
    have h := ZetaSeven.Assembly.assemble_stability_div hden hs hl
    simp only [error]
    calc
      ((267 * H - 266 / 500) / (267 - 261 * C)) * N T
          - 267 * (errorSource T + errorLocal T) / (267 - 261 * C)
          = ((267 * H - 266 / 500) * N T
              - 267 * (errorSource T + errorLocal T)) /
                (267 - 261 * C) := by ring
      _ ≤ S T := h
  have herror : error =o[atTop] N := by
    have hsum := hSourceError.add hLocalError
    have hscaled := hsum.const_mul_left
      (267 / (267 - 261 * C))
    exact hscaled.congr_left fun T => by
      simp only [error]
      ring
  exact eps_form_of_isLittleO hmain hN herror

/-- The exact `Cstar` specialization of `assemble_stability_eps`. -/
theorem assemble_Cstar_eps
    {H : ℝ} {N S D errorSource errorLocal : ℝ → ℝ}
    (hsource : ∀ᶠ T in atTop,
      H * N T + D T - errorSource T ≤ S T)
    (hlocal : ∀ᶠ T in atTop,
      (261 * ZetaSeven.Assembly.Cstar / 267) * S T
        - (266 / 133500) * N T - errorLocal T ≤ D T)
    (hN : ∀ᶠ T in atTop, 0 ≤ N T)
    (hSourceError : errorSource =o[atTop] N)
    (hLocalError : errorLocal =o[atTop] N) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (ZetaSeven.Assembly.sigma H - ε) * N T ≤ S T := by
  simpa only [ZetaSeven.Assembly.sigma] using
    assemble_stability_eps
      ZetaSeven.Assembly.Cstar_denominator_pos hsource hlocal hN
        hSourceError hLocalError

end ZetaSeven.AsymptoticAssembly
