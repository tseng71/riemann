# Claim ledger

Date: 2026-08-14

| Claim | Status | Evidence / remaining boundary |
| --- | --- | --- |
| This proves the Riemann hypothesis | **False** | No such claim is made. A positive-proportion result would not imply RH. |
| `F6(g) >= 38262312113/10^13` for all six nonnegative gaps | **Computer certified** | Arb subdivision: 822,433 nodes, 0 unresolved at 128/256 and 160/320 bits. A separate exact-rational LDL implementation rechecks both strong-convexity basins. A full independent interval implementation and Lean proof term remain open. |
| Stability-enhanced rank–trace inequality | **Lean proved** | `ZetaSeven.Stability.gram_defect_rank_trace`; no `sorry` or new axiom. |
| Spectral defect controls `2 * sum_{i<j} |G_ij|^2` | **Lean proved** | `ZetaSeven.BlockDefect`; clean compilation and axiom audit completed. |
| Simple-zero Gram split has remainder positive index at most `s₂+p` | **Lean proved** | `ZetaSeven.SimpleBlock`; instantiated against the concrete zeta-zero data. |
| Defect survives the finite tail seam from `A` to `G` | **Lean proved** | `ZetaSeven.SeamDefect.seamA_simple_defect`. |
| Defect survives the Theorem D source asymptotics | **Manuscript proved; abstract Lean layer proved** | Corollary 3.2 specializes Claude's normalized matrices and shows all comparison terms are `o(N)`. `ZetaSeven.ThmDDefect.thmD_simple_defect_abstract` checks the abstract algebra; a concrete end-to-end Lean specialization remains open. |
| Exact constant and linear-fractional assembly | **Lean proved** | `ZetaSeven.Assembly`; rational normalization checks the 261/262 threshold and denominator. |
| Epsilon-form asymptotic rearrangement | **Lean proved** | `ZetaSeven.AsymptoticAssembly`; takes explicit source/local `o(N)` errors and derives the exact resulting coefficient. |
| Consecutive seven-point window multiplicities | **Lean proved** | `ZetaSeven.WindowEnergy`; exact finite pair and gap charges, conditional only on the displayed `SevenPointClaim`. |
| Principal-block spectral pinching | **Lean proved** | `ZetaSeven.Pinching`; constructs and verifies the block-diagonal unitary and proves the arbitrary finite-partition defect inequality. |
| Concrete increasing-ordinate simple-zero Gram coordinates | **Lean proved** | `ZetaSeven.OrderedSimpleZeros`; enumerates the actual `S₁` subtype by `Fin (s₁(T))`, proves positive normalized consecutive gaps, reindexes the concrete Gram matrix, and preserves its spectral defect exactly. |
| Concrete consecutive 267-point Gram blocks | **Lean proved at an explicit comparison interface** | `ZetaSeven.ConcreteBlocks`; constructs every full principal block of the actual ordered Gram matrix, proves PSD, gap positivity and telescoping, and specializes the local defect theorem. Its displayed finite Gram-to-kernel error hypothesis remains analytic. |
| 267-offset finite aggregation | **Lean proved concretely** | `ZetaSeven.ConcreteShiftedPinching`; realizes all 267 partitions on `Fin S`, identifies every full block with a principal fiber, keeps both endpoint remainders in the `none` fiber, and proves the filtered-start pinching bound. |
| Concrete finite simple-zero assembly | **Lean proved at explicit analytic interfaces** | `ZetaSeven.ConcreteSimpleAssembly`; identifies local and global ordered gaps, aggregates the actual ordered simple-zero Gram blocks, and inserts the result into the exact finite simple-zero count. `SevenPointClaim` and the displayed per-block Gram-to-kernel errors remain inputs. |
| 267-point block defect from the local claim | **Lean proved conditional on explicit inputs** | `ZetaSeven.BlockEnergyDefect`; assumes `SevenPointClaim` and a displayed finite Gram-to-kernel comparison error. |
| `67.3025476837...%` bound | **Proved in an unreviewed computer-assisted manuscript** | The paper proves endpoint deletion, a uniform finite-Gram error, summability over 267 shifts, and final asymptotics. The local proposition is certified relative to the disclosed Arb/FLINT trust base. Independent specialist review and an end-to-end Lean proof remain open. |

## Status gate

The current revision may be called an **unreviewed computer-assisted proof**
because it contains a conventional analytic proof plus a replayable interval
certificate. It may be called **independently verified**, **fully formally
verified**, or **peer reviewed** only after the corresponding additional gate
is actually met:

- for full formal verification, a closed top-level Lean theorem or an
  independently checkable proof-carrying certificate;
- no `sorry`, `admit`, undisclosed axiom, or trusted Boolean shortcut in the
  new proof path;
- a machine-readable dependency and hash manifest;
- clean rebuild logs and axiom output;
- a paper whose theorem statement matches the formal statement exactly;
- for external acceptance, independent mathematical review of the analytic
  interface and certificate.
