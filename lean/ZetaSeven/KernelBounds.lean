/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ThmD.Window
import ZetaSeven.SharpCosineKernel

/-!
# Uniform bounds for the parameterized sharp kernel

These estimates make the passage `lambda -> 1` quantitative and uniform in
the normalized zero separation.
-/

noncomputable section

open MeasureTheory Real Set
open scoped Interval

namespace ZetaSeven.KernelBounds

open Zeta23.ThmD
open ZetaSeven.ParametricKernel
open ZetaSeven.SharpCosineKernel

/-- The sharp cosine mass is uniformly bounded away from zero on
`0 < lambda <= 1`. -/
theorem three_four_le_aStar {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    3 / 4 ≤ aStar lam := by
  have hpoint : ∀ s ∈ Set.Icc (-(1 : ℝ) / 2) ((1 : ℝ) / 2),
      3 / 4 ≤ vStar lam s := by
    intro s hs
    have habs : |s| ≤ (1 : ℝ) / 2 := by
      apply abs_le.mpr
      constructor <;> linarith [hs.1, hs.2]
    simpa using
      (cos_factor_ge (lam := lam) (L := 1) (u := s)
        hlam0 hlam1 one_pos habs)
  have hmono := intervalIntegral.integral_mono_on
    (μ := MeasureTheory.volume)
    (by norm_num : (-(1 : ℝ) / 2) ≤ ((1 : ℝ) / 2))
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by unfold vStar; fun_prop) _ _)
    hpoint
  norm_num at hmono
  unfold aStar
  convert hmono using 1 <;> norm_num

theorem aStar_pos {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    0 < aStar lam := by
  linarith [three_four_le_aStar hlam0 hlam1]

/-- The unnormalized cosine transform is bounded by the sharp mass. -/
theorem abs_integral_vStar_mul_cos_le_aStar {lam : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (x : ℝ) :
    |∫ s in (-(1 : ℝ) / 2)..((1 : ℝ) / 2),
        vStar lam s * Real.cos (2 * Real.pi * x * s)| ≤ aStar lam := by
  have hab : (-(1 : ℝ) / 2) ≤ ((1 : ℝ) / 2) := by norm_num
  have hv_nonneg : ∀ s ∈ Set.Icc (-(1 : ℝ) / 2) ((1 : ℝ) / 2),
      0 ≤ vStar lam s := by
    intro s hs
    have habs : |s| ≤ (1 : ℝ) / 2 := by
      apply abs_le.mpr
      constructor <;> linarith [hs.1, hs.2]
    have hcos := cos_factor_ge (lam := lam) (L := 1) (u := s)
      hlam0 hlam1 one_pos habs
    simpa using hcos.trans' (by norm_num : (0 : ℝ) ≤ 3 / 4)
  have hpoint : ∀ s ∈ Set.Icc (-(1 : ℝ) / 2) ((1 : ℝ) / 2),
      |vStar lam s * Real.cos (2 * Real.pi * x * s)| ≤ vStar lam s := by
    intro s hs
    rw [abs_mul, abs_of_nonneg (hv_nonneg s hs)]
    calc
      vStar lam s * |Real.cos (2 * Real.pi * x * s)|
          ≤ vStar lam s * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (hv_nonneg s hs)
      _ = vStar lam s := mul_one _
  calc
    |∫ s in (-(1 : ℝ) / 2)..((1 : ℝ) / 2),
        vStar lam s * Real.cos (2 * Real.pi * x * s)|
        ≤ ∫ s in (-(1 : ℝ) / 2)..((1 : ℝ) / 2),
            |vStar lam s * Real.cos (2 * Real.pi * x * s)| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ s in (-(1 : ℝ) / 2)..((1 : ℝ) / 2), vStar lam s := by
      apply intervalIntegral.integral_mono_on hab
      · exact Continuous.intervalIntegrable (by unfold vStar; fun_prop) _ _
      · exact Continuous.intervalIntegrable (by unfold vStar; fun_prop) _ _
      · exact hpoint
    _ = aStar lam := rfl

/-- The normalized sharp Fourier kernel has modulus at most one. -/
theorem abs_normalizedKernelAt_le_one {lam : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (x : ℝ) :
    |normalizedKernelAt lam x| ≤ 1 := by
  rw [← normalized_integral_eq_kernel hlam0 x, abs_div,
    abs_of_pos (aStar_pos hlam0 hlam1),
    div_le_one (aStar_pos hlam0 hlam1)]
  exact abs_integral_vStar_mul_cos_le_aStar hlam0 hlam1 x

/-- Uniform `L^1` Lipschitz estimate for the scale-free sharp profiles. -/
theorem integral_abs_vStar_sub_le (lam mu : ℝ) :
    (∫ s in (-(1 : ℝ) / 2)..((1 : ℝ) / 2),
        |vStar lam s - vStar mu s|) ≤
      (3 / 4) * |lam - mu| := by
  have hs32 : Real.sqrt 2 ≤ 3 / 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hpoint : ∀ s ∈ Set.Icc (-(1 : ℝ) / 2) ((1 : ℝ) / 2),
      |vStar lam s - vStar mu s| ≤ (3 / 4) * |lam - mu| := by
    intro s hs
    have habs : |s| ≤ (1 : ℝ) / 2 := by
      apply abs_le.mpr
      constructor <;> linarith [hs.1, hs.2]
    unfold vStar
    calc
      |Real.cos (Real.sqrt 2 * lam * s) -
          Real.cos (Real.sqrt 2 * mu * s)|
          ≤ |Real.sqrt 2 * lam * s - Real.sqrt 2 * mu * s| :=
        Real.abs_cos_sub_cos_le _ _
      _ = Real.sqrt 2 * |lam - mu| * |s| := by
        rw [show Real.sqrt 2 * lam * s - Real.sqrt 2 * mu * s =
            Real.sqrt 2 * (lam - mu) * s by ring,
          abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
      _ ≤ (3 / 2) * |lam - mu| * ((1 : ℝ) / 2) := by
        gcongr
      _ = (3 / 4) * |lam - mu| := by ring
  have hab : (-(1 : ℝ) / 2) ≤ ((1 : ℝ) / 2) := by norm_num
  have hmono := intervalIntegral.integral_mono_on
    (μ := MeasureTheory.volume) hab
    (Continuous.intervalIntegrable (by unfold vStar; fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    hpoint
  norm_num at hmono
  convert hmono using 1 <;> norm_num

/-- Consequently the sharp masses are Lipschitz with the same constant. -/
theorem abs_aStar_sub_le (lam mu : ℝ) :
    |aStar lam - aStar mu| ≤ (3 / 4) * |lam - mu| := by
  have hli : IntervalIntegrable (vStar lam) MeasureTheory.volume
      (-(1 : ℝ) / 2) ((1 : ℝ) / 2) :=
    Continuous.intervalIntegrable (by unfold vStar; fun_prop) _ _
  have hmi : IntervalIntegrable (vStar mu) MeasureTheory.volume
      (-(1 : ℝ) / 2) ((1 : ℝ) / 2) :=
    Continuous.intervalIntegrable (by unfold vStar; fun_prop) _ _
  unfold aStar
  rw [← intervalIntegral.integral_sub hli hmi]
  exact (intervalIntegral.abs_integral_le_integral_abs
      (by norm_num : (-(1 : ℝ) / 2) ≤ ((1 : ℝ) / 2))).trans
    (integral_abs_vStar_sub_le lam mu)

/-- The unnormalized cosine transforms are uniformly Lipschitz in the window
parameter. -/
theorem abs_integral_vStar_mul_cos_sub_le (lam mu x : ℝ) :
    |(∫ s in (-(1 : ℝ) / 2)..((1 : ℝ) / 2),
          vStar lam s * Real.cos (2 * Real.pi * x * s)) -
        ∫ s in (-(1 : ℝ) / 2)..((1 : ℝ) / 2),
          vStar mu s * Real.cos (2 * Real.pi * x * s)| ≤
      (3 / 4) * |lam - mu| := by
  have hab : (-(1 : ℝ) / 2) ≤ ((1 : ℝ) / 2) := by norm_num
  have hli : IntervalIntegrable
      (fun s => vStar lam s * Real.cos (2 * Real.pi * x * s))
      MeasureTheory.volume (-(1 : ℝ) / 2) ((1 : ℝ) / 2) :=
    Continuous.intervalIntegrable (by unfold vStar; fun_prop) _ _
  have hmi : IntervalIntegrable
      (fun s => vStar mu s * Real.cos (2 * Real.pi * x * s))
      MeasureTheory.volume (-(1 : ℝ) / 2) ((1 : ℝ) / 2) :=
    Continuous.intervalIntegrable (by unfold vStar; fun_prop) _ _
  rw [← intervalIntegral.integral_sub hli hmi]
  calc
    |∫ s in (-(1 : ℝ) / 2)..((1 : ℝ) / 2),
        (vStar lam s * Real.cos (2 * Real.pi * x * s) -
          vStar mu s * Real.cos (2 * Real.pi * x * s))|
        = |∫ s in (-(1 : ℝ) / 2)..((1 : ℝ) / 2),
            (vStar lam s - vStar mu s) *
              Real.cos (2 * Real.pi * x * s)| := by
          congr 2 with s
          ring
    _ ≤ ∫ s in (-(1 : ℝ) / 2)..((1 : ℝ) / 2),
          |(vStar lam s - vStar mu s) *
            Real.cos (2 * Real.pi * x * s)| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ s in (-(1 : ℝ) / 2)..((1 : ℝ) / 2),
          |vStar lam s - vStar mu s| := by
      apply intervalIntegral.integral_mono_on hab
      · exact Continuous.intervalIntegrable (by unfold vStar; fun_prop) _ _
      · exact Continuous.intervalIntegrable (by unfold vStar; fun_prop) _ _
      · intro s _
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _)
          (Real.abs_cos_le_one _)
    _ ≤ (3 / 4) * |lam - mu| := integral_abs_vStar_sub_le lam mu

/-- Uniform kernel Lipschitz bound on `0 < lambda, mu <= 1`. -/
theorem abs_normalizedKernelAt_sub_le_two {lam mu : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hmu0 : 0 < mu) (hmu1 : mu ≤ 1) (x : ℝ) :
    |normalizedKernelAt lam x - normalizedKernelAt mu x| ≤
      2 * |lam - mu| := by
  let A : ℝ := ∫ s in (-(1 : ℝ) / 2)..((1 : ℝ) / 2),
    vStar lam s * Real.cos (2 * Real.pi * x * s)
  let B : ℝ := ∫ s in (-(1 : ℝ) / 2)..((1 : ℝ) / 2),
    vStar mu s * Real.cos (2 * Real.pi * x * s)
  let a : ℝ := aStar lam
  let b : ℝ := aStar mu
  have ha34 : 3 / 4 ≤ a := three_four_le_aStar hlam0 hlam1
  have hb34 : 3 / 4 ≤ b := three_four_le_aStar hmu0 hmu1
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hAB : |A - B| ≤ (3 / 4) * |lam - mu| := by
    exact abs_integral_vStar_mul_cos_sub_le lam mu x
  have hB : |B| ≤ b := abs_integral_vStar_mul_cos_le_aStar hmu0 hmu1 x
  have hba : |b - a| ≤ (3 / 4) * |lam - mu| := by
    simpa [a, b, abs_sub_comm] using abs_aStar_sub_le mu lam
  have hid : A / a - B / b = (A - B) / a + B * (b - a) / (a * b) := by
    field_simp [ha0.ne', hb0.ne']
    ring
  have hterm1 : |(A - B) / a| ≤ |lam - mu| := by
    rw [abs_div, abs_of_pos ha0, div_le_iff₀ ha0]
    exact hAB.trans (by
      have hd : 0 ≤ |lam - mu| := abs_nonneg _
      nlinarith [mul_le_mul_of_nonneg_right ha34 hd])
  have hterm2 : |B * (b - a) / (a * b)| ≤ |lam - mu| := by
    simp only [abs_div, abs_mul, abs_of_pos ha0, abs_of_pos hb0,
      abs_of_pos (mul_pos ha0 hb0)]
    rw [div_le_iff₀ (mul_pos ha0 hb0)]
    calc
      |B| * |b - a| ≤ b * ((3 / 4) * |lam - mu|) :=
        mul_le_mul hB hba (abs_nonneg _) hb0.le
      _ ≤ b * (a * |lam - mu|) := by
        apply mul_le_mul_of_nonneg_left _ hb0.le
        have hd : 0 ≤ |lam - mu| := abs_nonneg _
        nlinarith [mul_le_mul_of_nonneg_right ha34 hd]
      _ = |lam - mu| * (a * b) := by ring
  rw [← normalized_integral_eq_kernel hlam0 x,
    ← normalized_integral_eq_kernel hmu0 x, show
      (∫ s in (-(1 : ℝ) / 2)..((1 : ℝ) / 2),
          vStar lam s * Real.cos (2 * Real.pi * x * s)) = A by rfl,
    show (∫ s in (-(1 : ℝ) / 2)..((1 : ℝ) / 2),
          vStar mu s * Real.cos (2 * Real.pi * x * s)) = B by rfl,
    show aStar lam = a by rfl, show aStar mu = b by rfl, hid]
  exact (abs_add_le _ _).trans (by linarith)

/-- Squaring the normalized kernel costs only a factor two because both
kernels have modulus at most one. -/
theorem abs_wAt_sub_le_four {lam mu : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hmu0 : 0 < mu) (hmu1 : mu ≤ 1) (x : ℝ) :
    |wAt lam x - wAt mu x| ≤ 4 * |lam - mu| := by
  have hdiff := abs_normalizedKernelAt_sub_le_two
    hlam0 hlam1 hmu0 hmu1 x
  have hsum :
      |normalizedKernelAt lam x + normalizedKernelAt mu x| ≤ 2 :=
    (abs_add_le _ _).trans (by
      linarith [abs_normalizedKernelAt_le_one hlam0 hlam1 x,
        abs_normalizedKernelAt_le_one hmu0 hmu1 x])
  unfold wAt
  rw [show normalizedKernelAt lam x ^ 2 - normalizedKernelAt mu x ^ 2 =
      (normalizedKernelAt lam x - normalizedKernelAt mu x) *
        (normalizedKernelAt lam x + normalizedKernelAt mu x) by ring,
    abs_mul]
  calc
    |normalizedKernelAt lam x - normalizedKernelAt mu x| *
        |normalizedKernelAt lam x + normalizedKernelAt mu x|
        ≤ (2 * |lam - mu|) * 2 :=
      mul_le_mul hdiff hsum (abs_nonneg _) (by positivity)
    _ = 4 * |lam - mu| := by ring

end ZetaSeven.KernelBounds
