# Trust base and verification boundary

## External interval certificate

The current finite certificate trusts CPython 3.12, `python-flint==0.8.0`,
Arb/FLINT, the operating system, hardware, and the included verifier source.
It regenerates transcendental interval tables and fails on any unresolved
terminal cell. The higher-precision run is a precision replay of the same
implementation, not an independent implementation.  The separate basin
checker changes the derivative, subdivision, and linear-algebra paths but
still uses Arb/FLINT for transcendental interval evaluation.

## Lean extension

Pinned versions:

- upstream: `anthropics/zeta-23-lean` commit
  `3635e74826a4c1fcece7d1cd2b6fa75e43a00510`;
- Lean: `leanprover/lean4:v4.33.0-rc2`;
- mathlib: `51e6992efd06126df61a496bebf8f49482a4e129`.

The completed declarations audited so far depend only on Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`. They include the finite
consecutive-window count, arbitrary principal-block spectral pinching,
abstract 267-offset aggregation, a conditional 267-point block bridge, an
abstract defect-preserving Theorem-D source inequality, all concrete shifted
partitions and endpoint fibers, their insertion into the finite simple-zero
count, and the epsilon-form algebra. They do not prove `SevenPointClaim` or
the required summably uniform analytic Gram-to-kernel comparison.

## Open Lean and trust-reduction obligations

1. Rational enclosures for `sqrt 2`, `pi`, `sin`, `cos`, and normalized sinc.
2. Proof-carrying bounds for all kernel and second-derivative cells.
3. Kernel replay of the 822,433-node subdivision forest.
4. Lean formalization of the manuscript's central endpoint deletion and
   summably uniform finite Gram-to-kernel error accounting.
5. A concrete Lean specialization of the abstract defect-preserving Theorem-D
   interface.

These obligations separate the current unreviewed computer-assisted theorem
from an end-to-end Lean theorem and from a certificate checked by a different
interval library. Independent specialist review is separately required
before claiming community acceptance.
