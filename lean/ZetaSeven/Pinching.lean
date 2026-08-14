/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0
-/
import ZetaSeven.Stability
import Mathlib.Data.Matrix.Block

/-!
# A Schur--Horn interface for spectral pinching

This module isolates the convex spectral step used by block pinching.  For a
positive semidefinite matrix, the sum of the penalty `psi` on the diagonal in
any unitary basis is no larger than the sum of `psi` on the spectrum.

In the block argument, the unitary basis is obtained by diagonalizing every
principal block separately.  The theorem below is the basis-independent part
of that argument; assembling those block eigenbases is a separate finite
indexing step.
-/

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset
open scoped ComplexOrder BigOperators

namespace ZetaSeven.Pinching

open ZetaSeven.Stability
open Zeta23.ZeroSide.RankTraceMult

variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Unitary similarity preserves the characteristic polynomial. -/
lemma charpoly_unitary_conjugate
    (M : Matrix ι ι 𝕜) (U : Matrix.unitaryGroup ι 𝕜) :
    (star (U : Matrix ι ι 𝕜) * M * (U : Matrix ι ι 𝕜)).charpoly =
      M.charpoly := by
  calc
    (star (U : Matrix ι ι 𝕜) * M * (U : Matrix ι ι 𝕜)).charpoly
        = ((U : Matrix ι ι 𝕜) *
            (star (U : Matrix ι ι 𝕜) * M)).charpoly :=
          Matrix.charpoly_mul_comm _ _
    _ = (((U : Matrix ι ι 𝕜) * star (U : Matrix ι ι 𝕜)) * M).charpoly := by
          rw [Matrix.mul_assoc]
    _ = M.charpoly := by
      rw [Unitary.mul_star_self_of_mem U.prop, one_mul]

/-- Unitary similarity preserves the indexed eigenvalue list of a Hermitian
matrix (including multiplicities and the canonical decreasing ordering). -/
lemma eigenvalues_unitary_conjugate
    {M : Matrix ι ι 𝕜} (hM : M.PosSemidef)
    (U : Matrix.unitaryGroup ι 𝕜) :
    ((hM.conjTranspose_mul_mul_same
        (U : Matrix ι ι 𝕜)).1.eigenvalues) = hM.1.eigenvalues := by
  apply ((hM.conjTranspose_mul_mul_same
    (U : Matrix ι ι 𝕜)).1.eigenvalues_eq_eigenvalues_iff hM.1).2
  exact charpoly_unitary_conjugate M U

/-- **Unitary-diagonal spectral pinching.**  Applying the convex penalty
`psi` to the diagonal entries in an arbitrary unitary basis cannot increase
the total beyond the spectral defect of the original PSD matrix. -/
theorem sum_psi_re_diag_unitary_le_spectralDefect
    {M : Matrix ι ι 𝕜} (hM : M.PosSemidef)
    (U : Matrix.unitaryGroup ι 𝕜) :
    (∑ j, psi (RCLike.re
        ((star (U : Matrix ι ι 𝕜) * M * (U : Matrix ι ι 𝕜)) j j)))
      ≤ spectralDefect hM := by
  let hA :
      (star (U : Matrix ι ι 𝕜) * M * (U : Matrix ι ι 𝕜)).PosSemidef :=
    hM.conjTranspose_mul_mul_same (U : Matrix ι ι 𝕜)
  have hschur := sum_gc_diag_le_sum_gc_eigenvalues hA (c := 2) (by norm_num)
  have heig : hA.1.eigenvalues = hM.1.eigenvalues :=
    eigenvalues_unitary_conjugate hM U
  unfold spectralDefect
  simp_rw [psi_eq_gc_add_one, Finset.sum_add_distrib]
  rw [heig] at hschur
  linarith

/-! ## Reindexing invariance -/

/-- Reindexing a PSD matrix along an equivalence preserves positivity. -/
theorem posSemidefReindex
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {M : Matrix ι ι 𝕜} (hM : M.PosSemidef) (e : ι ≃ κ) :
    (Matrix.reindex e e M).PosSemidef := by
  rw [Matrix.reindex_apply]
  exact hM.submatrix e.symm

/-- Spectral defect is invariant under a simultaneous row/column
reindexing.  The proof compares the canonical sorted eigenvalue lists, so it
also covers equivalences between index types that are not definitionally the
same cardinal. -/
theorem spectralDefect_reindex
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {M : Matrix ι ι 𝕜} (hM : M.PosSemidef) (e : ι ≃ κ) :
    spectralDefect (posSemidefReindex hM e) = spectralDefect hM := by
  have hchar : (Matrix.reindex e e M).charpoly = M.charpoly :=
    Matrix.charpoly_reindex e M
  have hlist :
      List.ofFn (posSemidefReindex hM e).1.eigenvalues₀ =
        List.ofFn hM.1.eigenvalues₀ := by
    rw [← (posSemidefReindex hM e).1.sort_roots_charpoly_eq_eigenvalues₀,
      ← hM.1.sort_roots_charpoly_eq_eigenvalues₀, hchar]
  unfold spectralDefect
  rw [RHLinalg.sum_eigenvalues_reindex _ psi,
    RHLinalg.sum_eigenvalues_reindex _ psi]
  have hsum := congrArg (fun xs : List ℝ => (xs.map psi).sum) hlist
  simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply] using hsum

/-! ## Principal-block pinching -/

section Blocks

variable {β : Type*} [Fintype β] [DecidableEq β]
variable {κ : β → Type*} [∀ b, Fintype (κ b)] [∀ b, DecidableEq (κ b)]

/-- The principal block selected by one fiber of a sigma-type partition. -/
def principalBlock (M : Matrix (Σ b, κ b) (Σ b, κ b) 𝕜) (b : β) :
    Matrix (κ b) (κ b) 𝕜 :=
  Matrix.blockDiag' M b

/-- Every principal block of a PSD matrix is PSD. -/
lemma principalBlock_posSemidef
    {M : Matrix (Σ b, κ b) (Σ b, κ b) 𝕜} (hM : M.PosSemidef)
    (b : β) : (principalBlock M b).PosSemidef := by
  exact hM.submatrix fun i => ⟨b, i⟩

/-- Extracting a diagonal block after left multiplication by a block-diagonal
matrix only sees the matching block. -/
lemma blockDiag'_blockDiagonal'_mul
    (A : ∀ b, Matrix (κ b) (κ b) 𝕜)
    (M : Matrix (Σ b, κ b) (Σ b, κ b) 𝕜) (b : β) :
    Matrix.blockDiag' (Matrix.blockDiagonal' A * M) b =
      A b * Matrix.blockDiag' M b := by
  ext i j
  simp only [Matrix.blockDiag'_apply, Matrix.mul_apply,
    ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Fintype.sum_eq_single b]
  · simp
  · intro b' hb'
    exact Finset.sum_eq_zero fun k _ => by
      rw [Matrix.blockDiagonal'_apply_ne A i k (Ne.symm hb')]
      simp

/-- Right-multiplication version of `blockDiag'_blockDiagonal'_mul`. -/
lemma blockDiag'_mul_blockDiagonal'
    (M : Matrix (Σ b, κ b) (Σ b, κ b) 𝕜)
    (A : ∀ b, Matrix (κ b) (κ b) 𝕜) (b : β) :
    Matrix.blockDiag' (M * Matrix.blockDiagonal' A) b =
      Matrix.blockDiag' M b * A b := by
  ext i j
  simp only [Matrix.blockDiag'_apply, Matrix.mul_apply,
    ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Fintype.sum_eq_single b]
  · simp
  · intro b' hb'
    exact Finset.sum_eq_zero fun k _ => by
      rw [Matrix.blockDiagonal'_apply_ne A k j hb']
      simp

/-- A block-diagonal family of unitary matrices is unitary on the sigma-type
direct sum. -/
def blockDiagonalUnitary
    (U : ∀ b, Matrix.unitaryGroup (κ b) 𝕜) :
    Matrix.unitaryGroup (Σ b, κ b) 𝕜 := by
  refine ⟨Matrix.blockDiagonal' fun b =>
    (U b : Matrix (κ b) (κ b) 𝕜), ?_⟩
  rw [Matrix.mem_unitaryGroup_iff']
  rw [Matrix.star_eq_conjTranspose, Matrix.blockDiagonal'_conjTranspose,
    ← Matrix.blockDiagonal'_mul]
  have hlocal :
      (fun b => (U b : Matrix (κ b) (κ b) 𝕜)ᴴ *
        (U b : Matrix (κ b) (κ b) 𝕜)) =
      (1 : ∀ b, Matrix (κ b) (κ b) 𝕜) := by
    funext b
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mul_self_of_mem (U b).prop
  rw [hlocal, Matrix.blockDiagonal'_one]

@[simp]
lemma blockDiagonalUnitary_coe
    (U : ∀ b, Matrix.unitaryGroup (κ b) 𝕜) :
    (blockDiagonalUnitary U : Matrix (Σ b, κ b) (Σ b, κ b) 𝕜) =
      Matrix.blockDiagonal' fun b => (U b : Matrix (κ b) (κ b) 𝕜) :=
  rfl

/-- Conjugating by a block-diagonal unitary restricts on each principal
block to conjugation by the corresponding unitary. -/
lemma principalBlock_conjugate_blockDiagonalUnitary
    (M : Matrix (Σ b, κ b) (Σ b, κ b) 𝕜)
    (U : ∀ b, Matrix.unitaryGroup (κ b) 𝕜) (b : β) :
    principalBlock
        (star (blockDiagonalUnitary U :
            Matrix (Σ b, κ b) (Σ b, κ b) 𝕜) * M *
          (blockDiagonalUnitary U :
            Matrix (Σ b, κ b) (Σ b, κ b) 𝕜)) b =
      star (U b : Matrix (κ b) (κ b) 𝕜) * principalBlock M b *
        (U b : Matrix (κ b) (κ b) 𝕜) := by
  unfold principalBlock
  rw [blockDiagonalUnitary_coe, blockDiag'_mul_blockDiagonal']
  rw [Matrix.star_eq_conjTranspose, Matrix.blockDiagonal'_conjTranspose,
    blockDiag'_blockDiagonal'_mul]
  rw [← Matrix.star_eq_conjTranspose]

/-- The blockwise eigenvector matrices, assembled into one global unitary. -/
def blockEigenvectorUnitary
    {M : Matrix (Σ b, κ b) (Σ b, κ b) 𝕜} (hM : M.PosSemidef) :
    Matrix.unitaryGroup (Σ b, κ b) 𝕜 :=
  blockDiagonalUnitary fun b =>
    (principalBlock_posSemidef hM b).1.eigenvectorUnitary

/-- In the assembled block eigenbasis, the diagonal entries are precisely
the eigenvalues of the principal blocks. -/
lemma re_diag_blockEigenvectorUnitary
    {M : Matrix (Σ b, κ b) (Σ b, κ b) 𝕜} (hM : M.PosSemidef)
    (b : β) (i : κ b) :
    RCLike.re
        ((star (blockEigenvectorUnitary hM :
              Matrix (Σ b, κ b) (Σ b, κ b) 𝕜) * M *
            (blockEigenvectorUnitary hM :
              Matrix (Σ b, κ b) (Σ b, κ b) 𝕜)) ⟨b, i⟩ ⟨b, i⟩) =
      (principalBlock_posSemidef hM b).1.eigenvalues i := by
  let hB := principalBlock_posSemidef hM b
  have hdiag := hB.1.conjStarAlgAut_star_eigenvectorUnitary
  have hblock :
      principalBlock
          (star (blockEigenvectorUnitary hM :
              Matrix (Σ b, κ b) (Σ b, κ b) 𝕜) * M *
            (blockEigenvectorUnitary hM :
              Matrix (Σ b, κ b) (Σ b, κ b) 𝕜)) b =
        star ((principalBlock_posSemidef hM b).1.eigenvectorUnitary :
            Matrix (κ b) (κ b) 𝕜) * principalBlock M b *
          ((principalBlock_posSemidef hM b).1.eigenvectorUnitary :
            Matrix (κ b) (κ b) 𝕜) := by
    simpa only [blockEigenvectorUnitary] using
      principalBlock_conjugate_blockDiagonalUnitary M
        (fun b => (principalBlock_posSemidef hM b).1.eigenvectorUnitary) b
  have hentry := congrFun (congrFun hblock i) i
  change RCLike.re
      ((principalBlock
        (star (blockEigenvectorUnitary hM :
            Matrix (Σ b, κ b) (Σ b, κ b) 𝕜) * M *
          (blockEigenvectorUnitary hM :
            Matrix (Σ b, κ b) (Σ b, κ b) 𝕜)) b) i i) = _
  rw [hentry]
  rw [show
      star ((principalBlock_posSemidef hM b).1.eigenvectorUnitary :
          Matrix (κ b) (κ b) 𝕜) * principalBlock M b *
        ((principalBlock_posSemidef hM b).1.eigenvectorUnitary :
          Matrix (κ b) (κ b) 𝕜) =
        Matrix.diagonal (RCLike.ofReal ∘
          (principalBlock_posSemidef hM b).1.eigenvalues) by
      simpa only [Unitary.conjStarAlgAut_star_apply] using hdiag]
  simp

/-- **Principal-block spectral pinching.**  For any finite partition encoded
as a sigma type, the sum of the spectral defects of all principal blocks is
bounded by the spectral defect of the full PSD matrix. -/
theorem sum_spectralDefect_principalBlock_le
    {M : Matrix (Σ b, κ b) (Σ b, κ b) 𝕜} (hM : M.PosSemidef) :
    (∑ b, spectralDefect (principalBlock_posSemidef hM b)) ≤
      spectralDefect hM := by
  have hpinch := sum_psi_re_diag_unitary_le_spectralDefect hM
    (blockEigenvectorUnitary hM)
  unfold spectralDefect at hpinch ⊢
  rw [Fintype.sum_sigma] at hpinch
  simpa only [re_diag_blockEigenvectorUnitary] using hpinch

end Blocks

end ZetaSeven.Pinching
