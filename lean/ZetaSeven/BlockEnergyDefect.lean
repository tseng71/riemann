/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0
-/
import ZetaSeven.WindowEnergy
import ZetaSeven.BlockDefect

/-!
# From the seven-point certificate to a 267-point block defect

This file joins the exact consecutive-window combinatorics to the spectral
block-defect inequality.  The only application-specific input left in the
main theorem is an explicit lower comparison between the finite Gram energy
and the normalized kernel energy, with a nonnegative error.
-/

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset
open scoped ComplexOrder BigOperators

namespace ZetaSeven.BlockEnergyDefect

open ZetaSeven.WindowEnergy
open ZetaSeven.BlockDefect
open ZetaSeven.Stability
open ZetaSeven.SevenPointSpec

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Finite 267-point block bridge.**  If the squared off-diagonal entries
of a PSD Gram block dominate the six-range normalized kernel energy up to
`err`, then its spectral defect obeys the paper's block lower bound.

No limiting argument is hidden here: `happrox` is the exact finite
Gram-to-kernel comparison that the analytic layer must supply. -/
theorem defect_lower_of_kernel_energy_approx
    (hseven : SevenPointClaim)
    (g : ℕ → ℝ) (hg : ∀ i, 0 ≤ g i)
    {M : Matrix (Fin 267) (Fin 267) 𝕜} (hM : M.PosSemidef)
    (err : ℝ) (herr : 0 ≤ err)
    (happrox : blockPairEnergy g 261 - err ≤
      2 * upperOffDiagEnergy M) :
    261 * ZetaSeven.Assembly.Cstar
        - (∑ j ∈ range 266, g j) / 500 - err
      ≤ spectralDefect hM := by
  have henergy := block_energy_of_sevenPointClaim hseven g hg 261
  norm_num at henergy
  have hshort :
      261 * ZetaSeven.Assembly.Cstar
          - (∑ j ∈ range 266, g j) / 500 - err
        ≤ 2 * upperOffDiagEnergy M := by
    linarith
  have hgap : 0 ≤ ∑ j ∈ range 266, g j :=
    Finset.sum_nonneg fun j _ => hg j
  have hcap :
      261 * ZetaSeven.Assembly.Cstar
          - (∑ j ∈ range 266, g j) / 500 - err ≤ 1 := by
    have hc := ZetaSeven.Assembly.Cstar_mul_261_lt_one
    norm_num at hc ⊢
    linarith
  exact (le_min hcap hshort).trans
    (min_one_two_mul_upperOffDiagEnergy_le_spectralDefect hM)

end ZetaSeven.BlockEnergyDefect
