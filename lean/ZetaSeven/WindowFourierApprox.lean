/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ThmD.Window

/-!
# Fourier error from tapering the sharp Montgomery--Taylor window

The upstream development proves that `phiD^2` differs in `L^1` from the
sharp cosine window by at most `2 * w`.  Here this is transferred, with no
asymptotic notation, to a uniform Fourier-transform error at every real
frequency.
-/

noncomputable section

open Complex MeasureTheory Real Set

namespace ZetaSeven.WindowFourierApprox

open Zeta23
open Zeta23.ThmD

/-- Multiplication by a real-frequency character preserves integrability. -/
theorem integrable_ofReal_mul_character {f : ℝ → ℝ}
    (hf : Integrable f) (x : ℝ) :
    Integrable (fun u : ℝ => (f u : ℂ) * Complex.exp (I * (x : ℂ) * u)) := by
  refine Integrable.mono' hf.norm ?_ ?_
  · exact
      (Complex.continuous_ofReal.comp_aestronglyMeasurable
          hf.aestronglyMeasurable).mul
        ((by fun_prop : Continuous
          (fun u : ℝ => Complex.exp (I * (x : ℂ) * u))).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall fun u => by
      simp [Zeta23.norm_cexp_I_mul]

/-- The paper-convention Fourier transform is `L^1`-Lipschitz on real
arguments. -/
theorem norm_paperFT_sub_le_integral_abs {f g : ℝ → ℝ}
    (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    ‖paperFT (fun u => (f u : ℂ)) x -
        paperFT (fun u => (g u : ℂ)) x‖ ≤
      ∫ u, |f u - g u| := by
  rw [Zeta23.paperFT_def, Zeta23.paperFT_def,
    ← MeasureTheory.integral_sub
      (integrable_ofReal_mul_character hf x)
      (integrable_ofReal_mul_character hg x)]
  calc
    ‖∫ u : ℝ,
        (f u : ℂ) * Complex.exp (I * (x : ℂ) * u) -
          (g u : ℂ) * Complex.exp (I * (x : ℂ) * u)‖
        = ‖∫ u : ℝ, ((f u - g u : ℝ) : ℂ) *
            Complex.exp (I * (x : ℂ) * u)‖ := by
              congr 2 with u
              push_cast
              ring
    _ ≤ ∫ u : ℝ, ‖((f u - g u : ℝ) : ℂ) *
          Complex.exp (I * (x : ℂ) * u)‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ u : ℝ, |f u - g u| := by
      congr 1 with u
      rw [← Complex.ofReal_sub, Complex.norm_real]
      simp [Zeta23.norm_cexp_I_mul]

/-- The square of the smooth window is integrable. -/
private theorem integrable_phiD_sq {rho : ℝ → ℝ} {lam L w : ℝ}
    (hrho : TaperProfile rho) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Integrable (fun u => phiD rho lam L w u ^ 2) := by
  have hL : 0 < L := by linarith
  have hcs : HasCompactSupport (fun u => phiD rho lam L w u ^ 2) := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (-(L / 2)) (L / 2)))
    intro u hu
    have habs : L / 2 ≤ |u| := by
      simp only [Set.mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with hu | hu
      · rw [abs_of_neg (by linarith : u < 0)]
        linarith
      · rw [abs_of_pos (by linarith : 0 < u)]
        linarith
    rw [phiD_eq_zero hrho hw habs, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  exact ((phiD_contDiff hrho hlam0 hlam1 hw hwL).pow 2).continuous
    |>.integrable_of_hasCompactSupport hcs

/-- The sharp comparison window is integrable. -/
theorem integrable_sharpW (lam L : ℝ) :
    Integrable (sharpW lam L) := by
  unfold sharpW
  exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
    ((by unfold vStar; fun_prop : Continuous
      (fun u : ℝ => vStar lam (u / L))).continuousOn.integrableOn_compact
        isCompact_Icc)

/-- Uniform Fourier error: tapering the sharp cosine window changes its
transform by at most `2 * w` at every real frequency. -/
theorem norm_VPhi_phiD_sub_sharp_le {rho : ℝ → ℝ} {lam L w : ℝ}
    (hrho : TaperProfile rho) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hw : 0 < w) (hwL : 2 * w ≤ L) (x : ℝ) :
    ‖Zeta23.AdmWindow.VPhi (phiD rho lam L w) x -
        paperFT (fun u => (sharpW lam L u : ℂ)) x‖ ≤ 2 * w := by
  exact (norm_paperFT_sub_le_integral_abs
      (integrable_phiD_sq hrho hlam0 hlam1 hw hwL)
      (integrable_sharpW lam L) x).trans
    (integral_abs_phiDsq_sub_sharp hrho hlam0 hlam1 hw hwL)

/-- The corresponding real-part estimate for the Gram kernel. -/
theorem abs_VPhiR_phiD_sub_sharp_re_le {rho : ℝ → ℝ} {lam L w : ℝ}
    (hrho : TaperProfile rho) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hw : 0 < w) (hwL : 2 * w ≤ L) (x : ℝ) :
    |Zeta23.AdmWindow.VPhiR (phiD rho lam L w) x -
        (paperFT (fun u => (sharpW lam L u : ℂ)) x).re| ≤ 2 * w := by
  calc
    |Zeta23.AdmWindow.VPhiR (phiD rho lam L w) x -
        (paperFT (fun u => (sharpW lam L u : ℂ)) x).re|
        = |(Zeta23.AdmWindow.VPhi (phiD rho lam L w) x -
            paperFT (fun u => (sharpW lam L u : ℂ)) x).re| := by
              rfl
    _ ≤ ‖Zeta23.AdmWindow.VPhi (phiD rho lam L w) x -
          paperFT (fun u => (sharpW lam L u : ℂ)) x‖ :=
      Complex.abs_re_le_norm _
    _ ≤ 2 * w :=
      norm_VPhi_phiD_sub_sharp_le hrho hlam0 hlam1 hw hwL x

end ZetaSeven.WindowFourierApprox
