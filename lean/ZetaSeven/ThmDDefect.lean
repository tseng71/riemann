/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ThmD.Mult
import ZetaSeven.AsymptoticAssembly
import ZetaSeven.SeamDefect

/-!
# Theorem-D source inequality with the simple-zero defect retained

The upstream multiplicity-aware Theorem D discards the favorable spectral
defect before its asymptotic endgame.  This module proves that the same trace
and tail estimates instead give a source inequality in which the defect is
still present and the remaining error is `o(N)`.

The seven-point local lower bound for this defect is intentionally not
assumed here.  It is the remaining analytic/computational bridge.
-/

noncomputable section

open Filter Asymptotics Topology Real RHLinalg
open scoped ComplexOrder

namespace ZetaSeven.ThmDDefect

open Zeta23
open Zeta23.Assembly
open Zeta23.ThmD

/-- The simple-zero Gram defect for the window-realizing Theorem-D family. -/
def simpleDefectD (Z : ZeroConfig) (P : Params) (T : ℝ) : ℝ :=
  ZetaSeven.Stability.spectralDefect
    (Matrix.posSemidef_conjTranspose_mul_self
      (ZetaSeven.SimpleBlock.zetaSimpleW Z T (P.atD T)
        (fun z => GzGp.phiHat_conj (P.atD T) T z)))

/-- Fixed-`T` trace substitution with an arbitrary favorable defect term. -/
theorem simple_lower_c_defect
    {S N NII trGh frGh B cinv R₁ R₂ D : ℝ} (hB : 0 ≤ B)
    (h₀ : 4 * trGh - frGh - 2 * N - 3 * NII
        - B * (4 + 2 * Real.sqrt frGh + B) + D ≤ S)
    (htr : |trGh - N| ≤ R₁) (hfr : frGh ≤ cinv * N + R₂) :
    (2 - cinv) * N + D - (4 * R₁ + R₂ + 3 * NII
        + B * (4 + 2 * Real.sqrt (cinv * N + R₂) + B)) ≤ S := by
  have h₁ : N - R₁ ≤ trGh := by
    have := (abs_le.mp htr).1
    linarith
  have h₂ : Real.sqrt frGh ≤ Real.sqrt (cinv * N + R₂) :=
    Real.sqrt_le_sqrt hfr
  nlinarith [h₀, h₁, h₂, hB, mul_le_mul_of_nonneg_left h₂ hB]

/-- Abstract Theorem-D source package with the simple-zero spectral defect
retained.  All remaining terms are combined into one explicitly constructed
`o(N)` error. -/
theorem thmD_simple_defect_abstract
    (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid)
    (hlam : P.lam < 1)
    (aT bT JT trG trG2 : ℝ → ℝ)
    (hTr : TracesBoundsD P aT bT JT trG trG2
      (fun T => (Z.N T (2 * T) : ℝ)))
    {c : ℝ} (hc0 : 0 < c)
    (hc : Tendsto
      (fun T => cRatio (P.lam1 T) (aT T) (bT T) (JT T))
      atTop (nhds c))
    (ha : ∀ᶠ T in atTop, 1 / 2 ≤ aT T ∧ aT T ≤ 1)
    (θ₀ : ℝ → ℝ)
    (hTail : ∀ᶠ T in atTop, TailInputs Z (P.atD T) T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop,
      θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop,
      (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop,
      Z.Gz (P.atD T) T = (P.atD T).Gp T)
    (hId : ∀ᶠ T in atTop,
      (P.atD T).trGtilde T = trG T ∧
      (P.atD T).trGtildeSq T = trG2 T ∧
      (P.atD T).a T = aT T)
    (hcalE : Tendsto P.calE atTop (nhds 0)) :
    ∃ error : ℝ → ℝ,
      error =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) ∧
      ∀ᶠ T in atTop,
        (2 - c⁻¹) * (Z.N T (2 * T) : ℝ)
          + simpleDefectD Z P T - error T
            ≤ (Z.N0s T (2 * T) : ℝ) := by
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hlam.le
  obtain ⟨C₁, hC₁, T₁, htr1⟩ := hTr.tr1
  obtain ⟨C₂, hC₂, T₂, hfr2⟩ := hTr.frhat
  obtain ⟨Cθ, hθ⟩ := hθ₀
  obtain ⟨CII, hII⟩ := hNII
  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set cinv : ℝ → ℝ := fun T =>
    (cRatio (P.lam1 T) (aT T) (bT T) (JT T))⁻¹ with hcinv
  set R₁ : ℝ → ℝ := fun T =>
    C₁ * Real.sqrt (P.X T) / aT T with hR₁
  set R₂ : ℝ → ℝ := fun T =>
    C₂ * P.calE T * (cinv T * N T) with hR₂
  set B : ℝ → ℝ := fun T =>
    θ₀ T / (aT T * P.L T) with hBdef
  set error : ℝ → ℝ := fun T =>
    (4 * R₁ T + R₂ T + 3 * (NII Z T : ℝ)
      + B T * (4 + 2 * Real.sqrt (cinv T * N T + R₂ T) + B T))
      + |cinv T - c⁻¹| * N T with herr
  have hcinv_to : Tendsto cinv atTop (nhds c⁻¹) := hc.inv₀ hc0.ne'
  have hmain : ∀ᶠ T in atTop,
      (2 - c⁻¹) * N T + simpleDefectD Z P T - error T
        ≤ (Z.N0s T (2 * T) : ℝ) := by
    filter_upwards [hTail, hGzGp, hId, ha,
      eventually_ge_atTop T₁, eventually_ge_atTop T₂,
      eventually_ge_atTop (0 : ℝ), eventually_l_pos,
      eventually_w8 hP]
      with T hTl hGG hid ha2 hT₁ hT₂ hT0 hl h8
    obtain ⟨hidtr, hidfr, hida⟩ := hid
    have hapos' : 0 < aT T := by linarith [ha2.1]
    have haposD : 0 < (P.atD T).a T := by
      rw [hida]
      exact hapos'
    have hLpos : 0 < P.L T := by
      simp only [Params.L]
      positivity
    have hA := ZetaSeven.SeamDefect.seamA_simple_defect
      hT0 (fun z => GzGp.phiHat_conj _ T z)
      (fun r => GzGp.phiHat_ofReal _ T r)
      (poissonSqD hP h8) hTl haposD hLpos
    have hrt :
        rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T))
          = (aT T * P.L T)⁻¹ * trG T := by
      rw [rtrace_hat, hGG, rtrace_tilde_Gp, hidtr, hida]
      rfl
    have hfr :
        frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))
          = ((aT T * P.L T)⁻¹) ^ 2 * trG2 T := by
      rw [frobSq_hat, hGG, frobSq_tilde_Gp, hidfr, hida]
      rfl
    have haL : (P.atD T).a T * (P.atD T).L T
        = aT T * P.L T := by
      rw [hida]
      rfl
    rw [hrt, hfr, haL] at hA
    have htr : |(aT T * P.L T)⁻¹ * trG T - N T| ≤ R₁ T :=
      trGhat_sub_N_le hapos' hLpos
        (by simpa only using htr1 T hT₁)
    have hfrb : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T
        ≤ cinv T * N T + R₂ T := by
      have h := hfr2 T hT₂
      simp only at h
      have h1 : trG2 T / (aT T * P.L T) ^ 2 - cinv T * N T
          ≤ C₂ * P.calE T * (cinv T * N T) := by
        rw [← mul_assoc] at h
        exact le_trans (le_trans (le_max_left _ 0) (le_abs_self _)) h
      have e : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T
          = trG2 T / (aT T * P.L T) ^ 2 := by
        rw [inv_pow, div_eq_inv_mul]
      rw [e]
      simp only [hR₂]
      linarith
    have hB₀ : 0 ≤ B T :=
      div_nonneg hTl.theta_nonneg (mul_pos hapos' hLpos).le
    have h := simple_lower_c_defect hB₀ hA htr hfrb
    have hN0 : 0 ≤ N T := Nat.cast_nonneg _
    have hcd :
        (2 - c⁻¹) * N T - |cinv T - c⁻¹| * N T
          ≤ (2 - cinv T) * N T := by
      have h1 := mul_le_mul_of_nonneg_right
        (le_abs_self (cinv T - c⁻¹)) hN0
      linarith [h1]
    simp only [simpleDefectD, herr, hR₁, hR₂, hBdef, hNdef] at h hcd ⊢
    linarith
  have hNtop : Tendsto N atTop atTop := tendsto_N_atTop Z H.RvM
  have o1 : R₁ =o[atTop] N := by
    have hbd : (fun T => C₁ / aT T) =O[atTop]
        (fun _ => (1 : ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 * C₁) ?_
      filter_upwards [ha] with T ha2
      rw [abs_of_nonneg (div_nonneg hC₁.le (by linarith [ha2.1]))]
      rw [div_le_iff₀ (by linarith [ha2.1])]
      nlinarith [ha2.1]
    have h := isLittleO_of_bdd_mul hbd
      (isLittleO_N_of_isLittleO_Tl Z H.RvM
        (isLittleO_sqrtX_Tl P hlam0 hlam1))
    exact h.congr_left fun T => by
      simp only [hR₁]
      ring
  have hcinv_bd : ∀ᶠ T in atTop,
      0 ≤ cinv T ∧ cinv T ≤ 2 * c⁻¹ := by
    have hcpos : (0 : ℝ) < c⁻¹ := inv_pos.mpr hc0
    filter_upwards
      [hcinv_to.eventually (eventually_ge_nhds hcpos),
       hcinv_to.eventually
        (eventually_le_nhds (show c⁻¹ < 2 * c⁻¹ by linarith))]
      with T h1 h2
    exact ⟨h1, h2⟩
  have hcinvO : cinv =O[atTop] (fun _ => (1 : ℝ)) := by
    refine isBigO_one_of_abs_le (C := 2 * c⁻¹) ?_
    filter_upwards [hcinv_bd] with T h
    rw [abs_of_nonneg h.1]
    exact h.2
  have o2 : R₂ =o[atTop] N := by
    have hcE0 : Tendsto (fun T => C₂ * P.calE T) atTop (nhds 0) := by
      simpa using hcalE.const_mul C₂
    have i1 : (fun T => cinv T * N T) =O[atTop] N := by
      have h := hcinvO.mul (isBigO_refl N atTop)
      simpa using h
    have h := ((isLittleO_one_iff ℝ).2 hcE0).mul_isBigO i1
    refine (h.congr_left fun T => ?_).congr_right fun T => by simp
    simp only [hR₂]
  have o3 : (fun T => (NII Z T : ℝ)) =o[atTop] N := by
    have hO : (fun T => (NII Z T : ℝ)) =O[atTop]
        (fun T => Real.sqrt T * l T) := by
      refine IsBigO.of_bound CII ?_
      filter_upwards [hII, eventually_l_pos] with T h hl
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
      simpa [mul_assoc] using h
    exact hO.trans_isLittleO
      (isLittleO_N_of_isLittleO_Tl Z H.RvM isLittleO_sqrt_mul_l_Tl)
  have o4 : Tendsto B atTop (nhds 0) := by
    have hup : Tendsto
        (fun T => 2 * |Cθ| *
          (l T * T ^ (P.lam / 2 - 1) / P.L T))
        atTop (nhds 0) := by
      simpa using
        (tendsto_theta_over_L P hlam0 hlam1).const_mul (2 * |Cθ|)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hTail, ha, eventually_l_pos]
        with T hTl ha2 hl
      have hLpos : 0 < P.L T := by
        simp only [Params.L]
        positivity
      exact div_nonneg hTl.theta_nonneg (by nlinarith [ha2.1])
    · filter_upwards [hTail, ha, eventually_l_pos, hθ,
        eventually_gt_atTop (0 : ℝ)]
        with T hTl ha2 hl hθT hT0
      have hLpos : 0 < P.L T := by
        simp only [Params.L]
        positivity
      have hapos' : 0 < aT T := by linarith [ha2.1]
      have hq : 0 ≤ l T * T ^ (P.lam / 2 - 1) / P.L T := by
        positivity
      simp only [hBdef]
      rw [div_le_iff₀ (mul_pos hapos' hLpos)]
      calc
        θ₀ T ≤ Cθ * l T * T ^ (P.lam / 2 - 1) := hθT
        _ ≤ |Cθ| * l T * T ^ (P.lam / 2 - 1) := by
          gcongr
          exact le_abs_self _
        _ = |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)
            * P.L T := by field_simp
        _ ≤ (2 * |Cθ| *
              (l T * T ^ (P.lam / 2 - 1) / P.L T))
              * (aT T * P.L T) := by
          have heq :
              |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)
                  * P.L T
                = (2 * |Cθ| *
                    (l T * T ^ (P.lam / 2 - 1) / P.L T))
                    * (1 / 2 * P.L T) := by ring
          rw [heq]
          gcongr
          exact ha2.1
  have o5 := err_isLittleO
    (R₁ := R₁) (R₂ := R₂)
    (NII := fun T => (NII Z T : ℝ)) (B := B)
    (cl := cinv) hNtop o1 o2 o3 o4 hcinv_bd
  have o6 : (fun T => |cinv T - c⁻¹| * N T) =o[atTop] N := by
    refine isLittleO_of_tendsto_zero_mul ?_
    have h : Tendsto (fun T => cinv T - c⁻¹)
        atTop (nhds 0) := by
      simpa using hcinv_to.sub_const c⁻¹
    simpa using h.abs
  have herror : error =o[atTop] N := o5.add o6
  refine ⟨error, ?_, ?_⟩
  · simpa only [hNdef] using herror
  · simpa only [hNdef] using hmain

end ZetaSeven.ThmDDefect
