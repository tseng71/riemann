/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0
-/
import ZetaSeven.WindowEnergy

/-!
# Exact arithmetic for the 267 shifted block partitions

This module proves the finite counting statements behind the shifted-block
average.  Full consecutive blocks are assigned to their starting index
modulo 267.  Summing over the 267 fibers counts every full block once, while
each adjacent gap lies in at most 266 such block spans.

The final theorem is deliberately stated for arbitrary block defects.  Its
fiber hypotheses are exactly what principal-block spectral pinching supplies
for each of the 267 shifted partitions.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace ZetaSeven.ShiftedPartitions

open ZetaSeven.WindowEnergy

/-- A finite sum is the sum of the fibers of any map to a finite type. -/
lemma sum_fibers_eq_sum
    {α β : Type*} [DecidableEq α] [Fintype β] [DecidableEq β]
    (s : Finset α) (offset : α → β) (f : α → ℝ) :
    (∑ r, ∑ k ∈ s with offset k = r, f k) = ∑ k ∈ s, f k := by
  calc
    (∑ r, ∑ k ∈ s with offset k = r, f k)
        = ∑ k ∈ s, ∑ r, if offset k = r then f k else 0 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k hk => ?_
          simp only [Finset.sum_filter]
    _ = ∑ k ∈ s, f k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Fintype.sum_eq_single (offset k)]
      · simp
      · intro r hr
        simp [Ne.symm hr]

/-- If every fiber sum is at most `D`, the total is at most the number of
fibers times `D`. -/
lemma sum_le_card_mul_of_fiber_le
    {α β : Type*} [DecidableEq α] [Fintype β] [DecidableEq β]
    (s : Finset α) (offset : α → β) (f : α → ℝ) (D : ℝ)
    (h : ∀ r, (∑ k ∈ s with offset k = r, f k) ≤ D) :
    (∑ k ∈ s, f k) ≤ Fintype.card β * D := by
  rw [← sum_fibers_eq_sum s offset f]
  calc
    (∑ r, ∑ k ∈ s with offset k = r, f k) ≤ ∑ _r : β, D :=
      Finset.sum_le_sum fun r _ => h r
    _ = Fintype.card β * D := by simp

/-- The residue class of a starting index among the 267 shifted
partitions. -/
def offset267 (k : ℕ) : Fin 267 :=
  ⟨k % 267, Nat.mod_lt _ (by norm_num)⟩

/-- Summing bounds over the 267 residue fibers gives the exact factor 267. -/
lemma sum_le_267_mul_of_offset267_fiber_le
    (s : Finset ℕ) (f : ℕ → ℝ) (D : ℝ)
    (h : ∀ r : Fin 267,
      (∑ k ∈ s with offset267 k = r, f k) ≤ D) :
    (∑ k ∈ s, f k) ≤ 267 * D := by
  simpa using sum_le_card_mul_of_fiber_le s offset267 f D h

/-- Across all full consecutive blocks of `m` points, each adjacent gap is
charged at most `m - 1` times. -/
lemma sum_full_block_spans_le
    (g : ℕ → ℝ) (hg : ∀ i, 0 ≤ g i)
    {S m : ℕ} (hm1 : 1 ≤ m) (hmS : m ≤ S) :
    (∑ k ∈ range (S - m + 1), ∑ a ∈ range (m - 1), g (k + a))
      ≤ ((m - 1 : ℕ) : ℝ) * ∑ j ∈ range (S - 1), g j := by
  have h := sum_shifted_windows_le g hg
    (n := S - m + 1) (q := m - 1)
  have harith : (S - m + 1) + (m - 1) - 1 = S - 1 := by omega
  simpa only [harith] using h

/-- The `m = 267` specialization: every adjacent gap is charged at most
266 times. -/
lemma sum_full_267_block_spans_le
    (g : ℕ → ℝ) (hg : ∀ i, 0 ≤ g i)
    {S : ℕ} (hS : 267 ≤ S) :
    (∑ k ∈ range (S - 266), ∑ a ∈ range 266, g (k + a))
      ≤ (266 : ℝ) * ∑ j ∈ range (S - 1), g j := by
  have h := sum_full_block_spans_le g hg
    (S := S) (m := 267) (by norm_num) hS
  have hstarts : S - 267 + 1 = S - 266 := by omega
  norm_num at h
  simpa only [hstarts] using h

/-- Exact finite 267-shift aggregation.

There are `S - 266` full consecutive 267-point blocks.  `hblock` is the
lower bound for each block defect; `hpinch` is the principal-block pinching
bound for each residue-class partition.  The conclusion includes every
finite endpoint term explicitly. -/
theorem aggregate_267_shifted_blocks
    {S : ℕ} (hS : 267 ≤ S)
    (C D : ℝ) (g E B : ℕ → ℝ)
    (hg : ∀ i, 0 ≤ g i)
    (hblock : ∀ k ∈ range (S - 266),
      261 * C - (∑ a ∈ range 266, g (k + a)) / 500 - E k ≤ B k)
    (hpinch : ∀ r : Fin 267,
      (∑ k ∈ range (S - 266) with offset267 k = r, B k) ≤ D) :
    ((S - 266 : ℕ) : ℝ) * (261 * C)
        - (266 / 500 : ℝ) * (∑ j ∈ range (S - 1), g j)
        - ∑ k ∈ range (S - 266), E k
      ≤ 267 * D := by
  have hblocks :
      (∑ k ∈ range (S - 266),
          (261 * C - (∑ a ∈ range 266, g (k + a)) / 500 - E k))
        ≤ ∑ k ∈ range (S - 266), B k :=
    Finset.sum_le_sum fun k hk => hblock k hk
  have hspan := sum_full_267_block_spans_le g hg hS
  have hfiber := sum_le_267_mul_of_offset267_fiber_le
    (range (S - 266)) B D hpinch
  have hexpand :
      (∑ k ∈ range (S - 266),
          (261 * C - (∑ a ∈ range 266, g (k + a)) / 500 - E k)) =
        ((S - 266 : ℕ) : ℝ) * (261 * C)
          - (∑ k ∈ range (S - 266),
              ∑ a ∈ range 266, g (k + a)) / 500
          - ∑ k ∈ range (S - 266), E k := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, ← Finset.sum_div]
  rw [hexpand] at hblocks
  linarith

end ZetaSeven.ShiftedPartitions
