/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0
-/
import ZetaSeven.ConcreteBlocks
import ZetaSeven.Pinching
import ZetaSeven.ShiftedPartitions

/-!
# Concrete shifted partitions and global spectral pinching

This module realizes each of the 267 residue-class partitions on an actual
finite index type `Fin S`.  Every full consecutive 267-point block becomes
one principal fiber.  The two endpoint remainders form the single `none`
fiber, whose spectral defect is discarded only by its proved
nonnegativity.

Consequently, the abstract fiberwise pinching hypothesis in
`aggregate_267_shifted_blocks` is discharged for the spectral defects of
concrete consecutive principal blocks.
-/

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset
open scoped ComplexOrder BigOperators

namespace ZetaSeven.ConcreteShiftedPinching

open ZetaSeven.Stability
open ZetaSeven.Pinching
open ZetaSeven.ShiftedPartitions
open ZetaSeven.ConcreteBlocks

/-- Full 267-point starts in one residue class. -/
def fullStarts (S : ℕ) (r : Fin 267) : Finset (Fin S) :=
  Finset.univ.filter fun k => k + 267 ≤ S ∧ offset267 k = r

abbrev FullStart (S : ℕ) (r : Fin 267) := ↥(fullStarts S r)

lemma FullStart.full {S : ℕ} {r : Fin 267} (k : FullStart S r) :
    (k : ℕ) + 267 ≤ S := by
  have h := k.2
  simp only [fullStarts, Finset.mem_filter, Finset.mem_univ, true_and] at h
  exact h.1

lemma FullStart.residue {S : ℕ} {r : Fin 267} (k : FullStart S r) :
    offset267 (k : ℕ) = r := by
  have h := k.2
  simp only [fullStarts, Finset.mem_filter, Finset.mem_univ, true_and] at h
  exact h.2

lemma map_fullStarts_eq_filter {S : ℕ} (hS : 267 ≤ S) (r : Fin 267) :
    (fullStarts S r).map Fin.valEmbedding =
      (range (S - 266)).filter fun k => offset267 k = r := by
  ext k
  simp only [Finset.mem_map, fullStarts, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_range, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨i, ⟨hfull, hres⟩, rfl⟩
    have hi : (i : ℕ) < S - 266 := by omega
    exact ⟨hi, hres⟩
  · rintro ⟨hk, hres⟩
    have hkS : k < S := by omega
    let i : Fin S := ⟨k, hkS⟩
    have hfull : (i : ℕ) + 267 ≤ S := by
      change k + 267 ≤ S
      omega
    have hres' : offset267 (i : ℕ) = r := by
      simpa [i] using hres
    exact ⟨i, ⟨hfull, hres'⟩, by simp [i]⟩

lemma sum_fullStarts_eq_filter {S : ℕ} (hS : 267 ≤ S)
    (r : Fin 267) (f : ℕ → ℝ) :
    (∑ k : FullStart S r, f k) =
      ∑ k ∈ range (S - 266) with offset267 k = r, f k := by
  rw [Finset.sum_coe_sort (fullStarts S r) (fun k : Fin S => f k)]
  change (∑ k ∈ fullStarts S r, f (Fin.valEmbedding k)) = _
  rw [← Finset.sum_map (fullStarts S r) Fin.valEmbedding f]
  rw [map_fullStarts_eq_filter hS r]

def Covers {S : ℕ} {r : Fin 267} (k : FullStart S r) (i : Fin S) : Prop :=
  (k : ℕ) ≤ i ∧ (i : ℕ) < (k : ℕ) + 267

lemma fullStart_eq_of_covers {S : ℕ} {r : Fin 267}
    {a b : FullStart S r} {i : Fin S}
    (ha : Covers a i) (hb : Covers b i) : a = b := by
  apply Subtype.ext
  apply Fin.ext
  have hmod : (a : ℕ) ≡ (b : ℕ) [MOD 267] := by
    have har := a.residue
    have hbr := b.residue
    unfold offset267 at har hbr
    have ha' := congrArg Fin.val har
    have hb' := congrArg Fin.val hbr
    exact ha'.trans hb'.symm
  have hab : (a : ℕ) ≤ (b : ℕ) :=
    hmod.le_of_lt_add (lt_of_le_of_lt ha.1 hb.2)
  have hba : (b : ℕ) ≤ (a : ℕ) :=
    hmod.symm.le_of_lt_add (lt_of_le_of_lt hb.1 ha.2)
  exact Nat.le_antisymm hab hba

/-- Partition label: `some k` on a full block and `none` on the two endpoint
remainders. -/
def shiftedLabel {S : ℕ} (r : Fin 267) (i : Fin S) :
    Option (FullStart S r) := by
  classical
  exact if h : ∃ k : FullStart S r, Covers k i then
    some (Classical.choose h)
  else none

lemma shiftedLabel_eq_some_of_covers {S : ℕ} (r : Fin 267)
    (k : FullStart S r) (i : Fin S) (hki : Covers k i) :
    shiftedLabel r i = some k := by
  classical
  let hex : ∃ q : FullStart S r, Covers q i := ⟨k, hki⟩
  have hc : Covers (Classical.choose hex) i := Classical.choose_spec hex
  have hlabel : shiftedLabel r i = some (Classical.choose hex) := by
    unfold shiftedLabel
    rw [dif_pos hex]
  rw [hlabel]
  congr 1
  exact fullStart_eq_of_covers hc hki

lemma covers_of_shiftedLabel_eq_some {S : ℕ} (r : Fin 267)
    {k : FullStart S r} {i : Fin S}
    (h : shiftedLabel r i = some k) : Covers k i := by
  unfold shiftedLabel at h
  split at h
  next hex =>
    have hc := Classical.choose_spec hex
    have heq : Classical.choose hex = k := by
      simpa only [Option.some.injEq] using h
    rwa [heq] at hc
  next hnone => simp at h

/-- A full block is exactly the `some k` fiber of the shifted partition. -/
def blockFiberEquiv {S : ℕ} (r : Fin 267) (k : FullStart S r) :
    Fin 267 ≃ {i : Fin S // shiftedLabel r i = some k} := by
  let f : Fin 267 → {i : Fin S // shiftedLabel r i = some k} := fun j =>
    ⟨blockIndex (k : ℕ) k.full j,
      shiftedLabel_eq_some_of_covers r k _ (by
        constructor <;> simp only [blockIndex] <;> omega)⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    apply blockIndex_injective (k : ℕ) k.full
    exact congrArg Subtype.val hab
  · intro i
    have hcover := covers_of_shiftedLabel_eq_some r i.2
    rcases hcover with ⟨hlo, hhi⟩
    let j : Fin 267 := ⟨(i : Fin S) - (k : ℕ), by omega⟩
    refine ⟨j, ?_⟩
    apply Subtype.ext
    apply Fin.ext
    simp only [f, blockIndex, j]
    omega

/-- Canonical equivalence from the original index to all partition fibers. -/
def shiftedPartitionEquiv {S : ℕ} (r : Fin 267) :
    Fin S ≃ Σ label : Option (FullStart S r),
      {i : Fin S // shiftedLabel r i = label} :=
  (Equiv.sigmaFiberEquiv (shiftedLabel r)).symm

variable {𝕜 : Type*} [RCLike 𝕜]

def shiftedPartitionMatrix {S : ℕ} (r : Fin 267)
    (M : Matrix (Fin S) (Fin S) 𝕜) :
    Matrix
      (Σ label : Option (FullStart S r),
        {i : Fin S // shiftedLabel r i = label})
      (Σ label : Option (FullStart S r),
        {i : Fin S // shiftedLabel r i = label}) 𝕜 :=
  Matrix.reindex (shiftedPartitionEquiv r) (shiftedPartitionEquiv r) M

theorem shiftedPartitionMatrix_posSemidef {S : ℕ} (r : Fin 267)
    {M : Matrix (Fin S) (Fin S) 𝕜} (hM : M.PosSemidef) :
    (shiftedPartitionMatrix r M).PosSemidef :=
  posSemidefReindex hM (shiftedPartitionEquiv r)

abbrev PartitionFiber {S : ℕ} (r : Fin 267)
    (label : Option (FullStart S r)) :=
  {i : Fin S // shiftedLabel r i = label}

/-- One principal block of the shifted partition. -/
def partitionBlock {S : ℕ} (r : Fin 267)
    (M : Matrix (Fin S) (Fin S) 𝕜)
    (label : Option (FullStart S r)) :
    Matrix (PartitionFiber r label) (PartitionFiber r label) 𝕜 :=
  principalBlock (shiftedPartitionMatrix r M) label

theorem partitionBlock_posSemidef {S : ℕ} (r : Fin 267)
    {M : Matrix (Fin S) (Fin S) 𝕜} (hM : M.PosSemidef)
    (label : Option (FullStart S r)) :
    (partitionBlock r M label).PosSemidef :=
  principalBlock_posSemidef
    (shiftedPartitionMatrix_posSemidef r hM) label

/-- The `some k` principal partition block is exactly the consecutive block
starting at `k`, after its canonical fiber reindexing. -/
theorem reindex_partitionBlock_some_eq_consecutive {S : ℕ} (r : Fin 267)
    (M : Matrix (Fin S) (Fin S) 𝕜) (k : FullStart S r) :
    Matrix.reindex (blockFiberEquiv r k).symm (blockFiberEquiv r k).symm
        (partitionBlock r M (some k)) =
      consecutivePrincipalBlock M (k : ℕ) k.full := by
  ext i j
  rfl

lemma spectralDefect_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι 𝕜} (hM : M.PosSemidef) :
    0 ≤ spectralDefect hM := by
  unfold spectralDefect
  exact Finset.sum_nonneg fun i _ => psi_nonneg _

lemma spectralDefect_congr
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M N : Matrix ι ι 𝕜} (hM : M.PosSemidef) (hN : N.PosSemidef)
    (hEq : M = N) : spectralDefect hM = spectralDefect hN := by
  subst N
  rfl

/-- The defect of a concrete consecutive block equals that of its principal
fiber in the shifted partition. -/
theorem spectralDefect_consecutive_eq_partition {S : ℕ} (r : Fin 267)
    {M : Matrix (Fin S) (Fin S) 𝕜} (hM : M.PosSemidef)
    (k : FullStart S r) :
    spectralDefect
        (consecutivePrincipalBlock_posSemidef hM (k : ℕ) k.full) =
      spectralDefect (partitionBlock_posSemidef r hM (some k)) := by
  have h := spectralDefect_reindex
    (partitionBlock_posSemidef r hM (some k)) (blockFiberEquiv r k).symm
  have hcongr := spectralDefect_congr
    (posSemidefReindex (partitionBlock_posSemidef r hM (some k))
      (blockFiberEquiv r k).symm)
    (consecutivePrincipalBlock_posSemidef hM (k : ℕ) k.full)
    (reindex_partitionBlock_some_eq_consecutive r M k)
  exact hcongr.symm.trans h

/-- **Concrete shifted-partition pinching.**  For one offset, the sum of
spectral defects of all actual disjoint full consecutive 267-point blocks is
bounded by the defect of the original PSD matrix.  Both endpoint remainders
are the single `none` fiber and are dropped only by nonnegativity. -/
theorem sum_consecutiveBlock_spectralDefect_le {S : ℕ} (r : Fin 267)
    {M : Matrix (Fin S) (Fin S) 𝕜} (hM : M.PosSemidef) :
    (∑ k : FullStart S r,
      spectralDefect
        (consecutivePrincipalBlock_posSemidef hM (k : ℕ) k.full)) ≤
      spectralDefect hM := by
  let hPart := shiftedPartitionMatrix_posSemidef r hM
  have hpinch := sum_spectralDefect_principalBlock_le hPart
  have hreindex := spectralDefect_reindex hM (shiftedPartitionEquiv r)
  calc
    (∑ k : FullStart S r,
        spectralDefect
          (consecutivePrincipalBlock_posSemidef hM (k : ℕ) k.full)) =
        ∑ k : FullStart S r,
          spectralDefect (partitionBlock_posSemidef r hM (some k)) := by
            apply Finset.sum_congr rfl
            intro k _
            exact spectralDefect_consecutive_eq_partition r hM k
    _ ≤ ∑ label : Option (FullStart S r),
          spectralDefect (partitionBlock_posSemidef r hM label) := by
            rw [Fintype.sum_option]
            exact le_add_of_nonneg_left
              (spectralDefect_nonneg (partitionBlock_posSemidef r hM none))
    _ ≤ spectralDefect hPart := hpinch
    _ = spectralDefect hM := hreindex

/-- The spectral defect at a natural-number start, extended by zero when no
full 267-point block starts there. -/
def blockDefectAt {S : ℕ}
    {M : Matrix (Fin S) (Fin S) 𝕜} (hM : M.PosSemidef) (k : ℕ) : ℝ :=
  if hk : k + 267 ≤ S then
    spectralDefect (consecutivePrincipalBlock_posSemidef hM k hk)
  else 0

/-- The concrete partition theorem in the filtered-start form expected by
the shifted-block aggregation theorem. -/
theorem offset267_fiber_blockDefectAt_le {S : ℕ} (hS : 267 ≤ S)
    (r : Fin 267) {M : Matrix (Fin S) (Fin S) 𝕜}
    (hM : M.PosSemidef) :
    (∑ k ∈ range (S - 266) with offset267 k = r, blockDefectAt hM k) ≤
      spectralDefect hM := by
  rw [← sum_fullStarts_eq_filter hS r (blockDefectAt hM)]
  simpa [blockDefectAt, FullStart.full] using
    (sum_consecutiveBlock_spectralDefect_le r hM)

/-- Exact 267-shift aggregation for concrete consecutive principal-block
defects.  In contrast with the abstract aggregation theorem, no fiberwise
pinching assumption remains: it is supplied by
`offset267_fiber_blockDefectAt_le`. -/
theorem aggregate_267_consecutiveBlock_defects
    {S : ℕ} (hS : 267 ≤ S)
    {M : Matrix (Fin S) (Fin S) 𝕜} (hM : M.PosSemidef)
    (C : ℝ) (g E : ℕ → ℝ)
    (hg : ∀ i, 0 ≤ g i)
    (hblock : ∀ k ∈ range (S - 266),
      261 * C - (∑ a ∈ range 266, g (k + a)) / 500 - E k ≤
        blockDefectAt hM k) :
    ((S - 266 : ℕ) : ℝ) * (261 * C)
        - (266 / 500 : ℝ) * (∑ j ∈ range (S - 1), g j)
        - ∑ k ∈ range (S - 266), E k
      ≤ 267 * spectralDefect hM := by
  exact aggregate_267_shifted_blocks hS C (spectralDefect hM)
    g E (blockDefectAt hM) hg hblock
      (fun r => offset267_fiber_blockDefectAt_le hS r hM)

end ZetaSeven.ConcreteShiftedPinching
