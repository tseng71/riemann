# Claim ledger

Date: 2026-08-12

| Claim | Status | Evidence / remaining boundary |
| --- | --- | --- |
| This proves the Riemann hypothesis | **False** | No such claim is made. A positive-proportion result would not imply RH. |
| `F6(g) >= 38262312113/10^13` for all six nonnegative gaps | **Externally certified** | Arb subdivision: 822,433 nodes, 0 unresolved; independently regenerated tables at 160/320 bits. A Lean proof term is still open. |
| Stability-enhanced rank–trace inequality | **Lean proved** | `ZetaSeven.Stability.gram_defect_rank_trace`; no `sorry` or new axiom. |
| Spectral defect controls `2 * sum_{i<j} |G_ij|^2` | **Lean proved** | `ZetaSeven.BlockDefect`; clean compilation and axiom audit completed. |
| Simple-zero Gram split has remainder positive index at most `s₂+p` | **Lean proved** | `ZetaSeven.SimpleBlock`; instantiated against the concrete zeta-zero data. |
| Defect survives the finite tail seam from `A` to `G` | **Lean proved** | `ZetaSeven.SeamDefect.seamA_simple_defect`. |
| Defect survives the abstract Theorem D source asymptotics | **Lean proved** | `ZetaSeven.ThmDDefect.thmD_simple_defect_abstract`; all remaining source-side error is packaged as `o(N)` under the pinned Theorem-D trace/tail hypotheses. Concrete top-level specialization remains open. |
| Exact constant and linear-fractional assembly | **Lean proved** | `ZetaSeven.Assembly`; rational normalization checks the 261/262 threshold and denominator. |
| Epsilon-form asymptotic rearrangement | **Lean proved** | `ZetaSeven.AsymptoticAssembly`; takes explicit source/local `o(N)` errors and derives the exact candidate coefficient. |
| Consecutive seven-point window multiplicities | **Lean proved** | `ZetaSeven.WindowEnergy`; exact finite pair and gap charges, conditional only on the displayed `SevenPointClaim`. |
| Principal-block spectral pinching | **Lean proved** | `ZetaSeven.Pinching`; constructs and verifies the block-diagonal unitary and proves the arbitrary finite-partition defect inequality. |
| Concrete increasing-ordinate simple-zero Gram coordinates | **Lean proved** | `ZetaSeven.OrderedSimpleZeros`; enumerates the actual `S₁` subtype by `Fin (s₁(T))`, proves positive normalized consecutive gaps, reindexes the concrete Gram matrix, and preserves its spectral defect exactly. |
| 267-offset finite aggregation | **Lean proved at the abstract fiber interface** | `ZetaSeven.ShiftedPartitions`; proves exact residue-fiber counting and the 266-fold gap charge. Concrete residue partitions, retained central sublists, and endpoint remainder wiring remain open. |
| 267-point block defect from the local claim | **Lean proved conditional on explicit inputs** | `ZetaSeven.BlockEnergyDefect`; assumes `SevenPointClaim` and a displayed finite Gram-to-kernel comparison error. |
| Candidate `67.3025476837...%` bound | **Open end-to-end** | Requires proof-carrying interval replay, retained-central-sublist partition/remainder and endpoint integration, uniform Gram-to-kernel error control, and top-level specialization of the defect-preserving interface. |

## Release gate

The candidate proportion may be promoted from “open” to “proved” only if all
of the following are present in one immutable revision:

- a closed top-level Lean theorem or an explicitly documented equivalent
  proof object;
- no `sorry`, `admit`, undisclosed axiom, or trusted Boolean shortcut in the
  new proof path;
- a machine-readable dependency and hash manifest;
- clean rebuild logs and axiom output;
- a paper whose theorem statement matches the formal statement exactly;
- independent mathematical review of the analytic interface.
