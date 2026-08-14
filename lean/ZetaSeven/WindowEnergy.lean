/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0
-/
import ZetaSeven.SevenPointSpec
import Mathlib.Algebra.BigOperators.Field

/-!
# Consecutive seven-point windows and finite block energy

This module proves the exact finite combinatorial step that converts the
six-gap local functional into a block-energy inequality.  No zeta-zero or
asymptotic input is used here.

If there are `n` consecutive seven-point windows, there are `n + 5` gaps.
A separation spanning `r` gaps occurs in at most `7 - r` windows; the local
coefficient `2 / (7 - r)` therefore charges it at most twice.  Each gap is
charged at most six times by the pressure term, giving the factor `1 / 500`.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace ZetaSeven.WindowEnergy

open ZetaSeven.SevenPointSpec

/-- A shifted sum of a nonnegative sequence is bounded by any longer prefix
that contains all its indices. -/
lemma sum_range_shift_le_sum_range
    (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i)
    {n q a : ℕ} (ha : a < q) :
    (∑ i ∈ range n, f (i + a))
      ≤ ∑ j ∈ range (n + q - 1), f j := by
  have hprefix :
      (∑ i ∈ range n, f (i + a)) ≤ ∑ j ∈ range (a + n), f j := by
    rw [sum_range_add]
    have hnonneg : 0 ≤ ∑ j ∈ range a, f j :=
      sum_nonneg fun j _ => hf j
    simpa [Nat.add_comm] using
      (le_add_of_nonneg_left hnonneg :
        (∑ i ∈ range n, f (a + i))
          ≤ (∑ j ∈ range a, f j) + ∑ i ∈ range n, f (a + i))
  have hlen : a + n ≤ n + q - 1 := by omega
  exact hprefix.trans <|
    sum_le_sum_of_subset_of_nonneg (range_mono hlen)
      (fun j _ _ => hf j)

/-- In `n` windows of width `q`, every global index is charged at most `q`
times. -/
lemma sum_shifted_windows_le
    (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i)
    {n q : ℕ} :
    (∑ i ∈ range n, ∑ a ∈ range q, f (i + a))
      ≤ q * ∑ j ∈ range (n + q - 1), f j := by
  calc
    (∑ i ∈ range n, ∑ a ∈ range q, f (i + a))
        = ∑ a ∈ range q, ∑ i ∈ range n, f (i + a) := sum_comm
    _ ≤ ∑ _a ∈ range q, ∑ j ∈ range (n + q - 1), f j := by
      refine sum_le_sum fun a ha => ?_
      exact sum_range_shift_le_sum_range f hf (mem_range.mp ha)
    _ = q * ∑ j ∈ range (n + q - 1), f j := by simp

/-- Squared overlap for one adjacent gap. -/
def pair1 (g : ℕ → ℝ) (i : ℕ) : ℝ := w (g i)

/-- Squared overlap for a separation spanning two adjacent gaps. -/
def pair2 (g : ℕ → ℝ) (i : ℕ) : ℝ := w (g i + g (i + 1))

/-- Squared overlap for a separation spanning three adjacent gaps. -/
def pair3 (g : ℕ → ℝ) (i : ℕ) : ℝ :=
  w (g i + g (i + 1) + g (i + 2))

/-- Squared overlap for a separation spanning four adjacent gaps. -/
def pair4 (g : ℕ → ℝ) (i : ℕ) : ℝ :=
  w (g i + g (i + 1) + g (i + 2) + g (i + 3))

/-- Squared overlap for a separation spanning five adjacent gaps. -/
def pair5 (g : ℕ → ℝ) (i : ℕ) : ℝ :=
  w (g i + g (i + 1) + g (i + 2) + g (i + 3) + g (i + 4))

/-- Squared overlap for a separation spanning six adjacent gaps. -/
def pair6 (g : ℕ → ℝ) (i : ℕ) : ℝ :=
  w (g i + g (i + 1) + g (i + 2) + g (i + 3) + g (i + 4) + g (i + 5))

lemma pair1_nonneg (g : ℕ → ℝ) (i : ℕ) : 0 ≤ pair1 g i := by
  exact sq_nonneg _

lemma pair2_nonneg (g : ℕ → ℝ) (i : ℕ) : 0 ≤ pair2 g i := by
  exact sq_nonneg _

lemma pair3_nonneg (g : ℕ → ℝ) (i : ℕ) : 0 ≤ pair3 g i := by
  exact sq_nonneg _

lemma pair4_nonneg (g : ℕ → ℝ) (i : ℕ) : 0 ≤ pair4 g i := by
  exact sq_nonneg _

lemma pair5_nonneg (g : ℕ → ℝ) (i : ℕ) : 0 ≤ pair5 g i := by
  exact sq_nonneg _

lemma pair6_nonneg (g : ℕ → ℝ) (i : ℕ) : 0 ≤ pair6 g i := by
  exact sq_nonneg _

/-- The paper's local functional at the window starting at gap `i`. -/
def windowAt (g : ℕ → ℝ) (i : ℕ) : ℝ :=
  F6 (g i) (g (i + 1)) (g (i + 2))
    (g (i + 3)) (g (i + 4)) (g (i + 5))

/-- Exact representation of a local window as six shifted pair sums. -/
lemma windowAt_eq (g : ℕ → ℝ) (i : ℕ) :
    windowAt g i =
      (∑ a ∈ range 6, g (i + a)) / 3000
      + (1 / 3) * ∑ a ∈ range 6, pair1 g (i + a)
      + (2 / 5) * ∑ a ∈ range 5, pair2 g (i + a)
      + (1 / 2) * ∑ a ∈ range 4, pair3 g (i + a)
      + (2 / 3) * ∑ a ∈ range 3, pair4 g (i + a)
      + ∑ a ∈ range 2, pair5 g (i + a)
      + 2 * ∑ a ∈ range 1, pair6 g (i + a) := by
  simp [windowAt, F6, pair1, pair2, pair3, pair4, pair5, pair6,
    sum_range_succ]
  ring

/-- Twice the total short-range pair energy in a block containing `n`
consecutive seven-point windows. -/
def blockPairEnergy (g : ℕ → ℝ) (n : ℕ) : ℝ :=
  2 * ((∑ j ∈ range (n + 5), pair1 g j)
    + (∑ j ∈ range (n + 4), pair2 g j)
    + (∑ j ∈ range (n + 3), pair3 g j)
    + (∑ j ∈ range (n + 2), pair4 g j)
    + (∑ j ∈ range (n + 1), pair5 g j)
    + (∑ j ∈ range n, pair6 g j))

/-- Exact finite block inequality obtained by summing the seven-point local
claim over all consecutive windows. -/
theorem sum_windowAt_le_blockPairEnergy_add_pressure
    (g : ℕ → ℝ) (hg : ∀ i, 0 ≤ g i) (n : ℕ) :
    (∑ i ∈ range n, windowAt g i)
      ≤ blockPairEnergy g n + (∑ j ∈ range (n + 5), g j) / 500 := by
  have hgap := sum_shifted_windows_le g hg (n := n) (q := 6)
  have h1 := sum_shifted_windows_le (pair1 g) (pair1_nonneg g)
    (n := n) (q := 6)
  have h2 := sum_shifted_windows_le (pair2 g) (pair2_nonneg g)
    (n := n) (q := 5)
  have h3 := sum_shifted_windows_le (pair3 g) (pair3_nonneg g)
    (n := n) (q := 4)
  have h4 := sum_shifted_windows_le (pair4 g) (pair4_nonneg g)
    (n := n) (q := 3)
  have h5 := sum_shifted_windows_le (pair5 g) (pair5_nonneg g)
    (n := n) (q := 2)
  have hgap' :
      (∑ i ∈ range n, ∑ a ∈ range 6, g (i + a)) / 3000
        ≤ (∑ j ∈ range (n + 5), g j) / 500 := by
    norm_num at hgap ⊢
    linarith
  have h1' :
      (1 / 3 : ℝ) * (∑ i ∈ range n, ∑ a ∈ range 6, pair1 g (i + a))
        ≤ 2 * ∑ j ∈ range (n + 5), pair1 g j := by
    norm_num at h1 ⊢
    linarith
  have h2' :
      (2 / 5 : ℝ) * (∑ i ∈ range n, ∑ a ∈ range 5, pair2 g (i + a))
        ≤ 2 * ∑ j ∈ range (n + 4), pair2 g j := by
    norm_num at h2 ⊢
    linarith
  have h3' :
      (1 / 2 : ℝ) * (∑ i ∈ range n, ∑ a ∈ range 4, pair3 g (i + a))
        ≤ 2 * ∑ j ∈ range (n + 3), pair3 g j := by
    norm_num at h3 ⊢
    linarith
  have h4' :
      (2 / 3 : ℝ) * (∑ i ∈ range n, ∑ a ∈ range 3, pair4 g (i + a))
        ≤ 2 * ∑ j ∈ range (n + 2), pair4 g j := by
    norm_num at h4 ⊢
    linarith
  have h5' :
      (∑ i ∈ range n, ∑ a ∈ range 2, pair5 g (i + a))
        ≤ 2 * ∑ j ∈ range (n + 1), pair5 g j := by
    norm_num at h5 ⊢
    linarith
  have hsum :
      (∑ i ∈ range n, windowAt g i) =
        (∑ i ∈ range n, ∑ a ∈ range 6, g (i + a)) / 3000
        + (1 / 3) * (∑ i ∈ range n,
            ∑ a ∈ range 6, pair1 g (i + a))
        + (2 / 5) * (∑ i ∈ range n,
            ∑ a ∈ range 5, pair2 g (i + a))
        + (1 / 2) * (∑ i ∈ range n,
            ∑ a ∈ range 4, pair3 g (i + a))
        + (2 / 3) * (∑ i ∈ range n,
            ∑ a ∈ range 3, pair4 g (i + a))
        + (∑ i ∈ range n, ∑ a ∈ range 2, pair5 g (i + a))
        + 2 * (∑ i ∈ range n, pair6 g i) := by
    simp_rw [windowAt_eq]
    simp only [sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum]
    simp
  rw [hsum]
  unfold blockPairEnergy
  linarith

/-- The certified local claim supplies one copy of `Cstar` per window. -/
theorem Cstar_mul_le_sum_windowAt
    (hseven : SevenPointClaim) (g : ℕ → ℝ) (hg : ∀ i, 0 ≤ g i) (n : ℕ) :
    (n : ℝ) * ZetaSeven.Assembly.Cstar
      ≤ ∑ i ∈ range n, windowAt g i := by
  calc
    (n : ℝ) * ZetaSeven.Assembly.Cstar
        = ∑ _i ∈ range n, ZetaSeven.Assembly.Cstar := by simp
    _ ≤ ∑ i ∈ range n, windowAt g i := by
      refine sum_le_sum fun i _ => ?_
      exact hseven _ _ _ _ _ _ (hg i) (hg (i + 1)) (hg (i + 2))
        (hg (i + 3)) (hg (i + 4)) (hg (i + 5))

/-- Finite consecutive-block energy inequality, conditional only on the
explicitly displayed local certificate proposition. -/
theorem block_energy_of_sevenPointClaim
    (hseven : SevenPointClaim) (g : ℕ → ℝ) (hg : ∀ i, 0 ≤ g i) (n : ℕ) :
    (n : ℝ) * ZetaSeven.Assembly.Cstar
      ≤ blockPairEnergy g n + (∑ j ∈ range (n + 5), g j) / 500 := by
  exact (Cstar_mul_le_sum_windowAt hseven g hg n).trans
    (sum_windowAt_le_blockPairEnergy_add_pressure g hg n)

end ZetaSeven.WindowEnergy
