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
| Candidate `67.3025476837...%` bound | **Open end-to-end** | Requires the verified interval replay and the local-to-global block pinching/window/endpoint formalization, followed by concrete specialization of the defect-preserving interface. |

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
