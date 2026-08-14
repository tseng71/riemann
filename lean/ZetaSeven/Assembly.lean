/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0
-/
/-
# Exact arithmetic for the seven-point stability assembly

This file is deliberately independent of the analytic zero-density inputs.
It verifies the rational constant, the 261/262 window threshold, and the
algebraic rearrangement that turns a local defect lower bound into the global
simple-zero proportion.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ZetaSeven.Assembly

noncomputable section

/-- The certified seven-point local constant. -/
def Cstar : ℝ := 38262312113 / 10000000000000

lemma Cstar_pos : 0 < Cstar := by
  norm_num [Cstar]

/-- 261 copies are still below unit pressure. -/
lemma Cstar_mul_261_lt_one : 261 * Cstar < 1 := by
  norm_num [Cstar]

/-- 262 copies cross unit pressure. -/
lemma one_lt_Cstar_mul_262 : 1 < 262 * Cstar := by
  norm_num [Cstar]

lemma Cstar_denominator_pos : 0 < 267 - 261 * Cstar := by
  norm_num [Cstar]

lemma Cstar_block_267_exact :
    261 * Cstar = 9986463461493 / 10000000000000 := by
  norm_num [Cstar]

lemma Cstar_block_268_exact :
    262 * Cstar = 10024725773606 / 10000000000000 := by
  norm_num [Cstar]

/-- Finite zero-count bookkeeping following the strengthened matrix bound. -/
theorem finite_zero_counting
    {frob traceA simple multiplePairs offLinePairs total defect : ℝ}
    (hstable : 4 * traceA - 3 * simple - 4 * multiplePairs
        - 4 * offLinePairs + defect ≤ frob)
    (hcount : simple + 2 * multiplePairs + 2 * offLinePairs ≤ total) :
    4 * traceA - frob - 2 * total + defect ≤ simple := by
  linarith

/-- Pure algebraic assembly with explicit error terms.

`hsource` retains the spectral defect in the analytic source inequality;
`hlocal` is the seven-point/window lower bound for that defect.  No analytic
assumption is hidden in this lemma.
-/
theorem assemble_stability
    {H C N S D errorSource errorLocal : ℝ}
    (hsource : H * N + D - errorSource ≤ S)
    (hlocal : (261 * C / 267) * S - (266 / 133500) * N - errorLocal ≤ D) :
    (267 - 261 * C) * S
      ≥ (267 * H - 266 / 500) * N - 267 * (errorSource + errorLocal) := by
  linarith

/-- Quotient form of `assemble_stability`, valid when the denominator is
positive. -/
theorem assemble_stability_div
    {H C N S D errorSource errorLocal : ℝ}
    (hden : 0 < 267 - 261 * C)
    (hsource : H * N + D - errorSource ≤ S)
    (hlocal : (261 * C / 267) * S - (266 / 133500) * N - errorLocal ≤ D) :
    ((267 * H - 266 / 500) * N - 267 * (errorSource + errorLocal)) /
        (267 - 261 * C) ≤ S := by
  apply (div_le_iff₀ hden).2
  simpa [mul_comm] using assemble_stability hsource hlocal

/-- The exact symbolic coefficient produced by the certified value `Cstar`. -/
def sigma (H : ℝ) : ℝ :=
  (267 * H - 266 / 500) / (267 - 261 * Cstar)

lemma sigma_exact_form (H : ℝ) :
    sigma H =
      (2670000000000000 * H - 5320000000000) / 2660013536538507 := by
  norm_num [sigma, Cstar]
  ring

end
end ZetaSeven.Assembly
