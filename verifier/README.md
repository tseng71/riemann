# Computer-assisted seven-point candidate refinement

This artifact accompanies the peer-review draft
*A Computer-Assisted Seven-Point Candidate Refinement for Simple Zeros of the
Riemann Zeta Function*.  It rigorously verifies the finite inequality

\[
\mathcal F_6(g_1,\ldots,g_6)
\ge \frac{38\,262\,312\,113}{10^{13}}
=0.0038262312113
\qquad(g_i\ge 0).
\]

Combined with the analytic framework stated in Theorem D of Claude's 2026
paper, the inequality gives the candidate bound

\[
\liminf_{T\to\infty}
\frac{N_0^s(T,2T)}{N(T,2T)}
\ge 0.6730254768378743181\ldots .
\]

> **Status.** This is an AI-assisted, unreviewed research artifact.  It does
> not prove the Riemann hypothesis.  The finite interval certificate has been
> run successfully at two Arb precision settings.  A pinned Lean companion
> proves the new finite-dimensional stability, spectral-energy, and exact
> assembly lemmas and an abstract defect-preserving Theorem D source
> inequality without `sorry`.  It does not yet replay the Arb certificate or
> prove the concrete local-to-global seven-point specialization (including
> central-window replacement, shifted partitions, endpoint deletion, and
> uniform error control).  No part of the proposed improvement has yet
> received independent expert review.

## Reproduce the certificate

The reference environment is CPython 3.12 with `python-flint==0.8.0`.

```bash
python3.12 -m venv .venv
source .venv/bin/activate
python -m pip install --require-hashes -r requirements.lock
PYTHONPATH=src python -m unittest discover -s tests -v
PYTHONPATH=src python scripts/verify_release.py
```

The release verifier reconstructs every transcendental interval table and
compares all deterministic fields with
`certificates/seven-point.expected.json`.  A terminal cell that cannot be
discarded is a hard failure.  The higher-precision rerun is:

```bash
PYTHONPATH=src python scripts/verify_cross_precision.py
```

The exhaustive searches take several minutes each on a typical x86_64
machine.

## What is certified

- grid mesh `1/4000` and exact rational target `38262312113/10^13`;
- Arb enclosures of the normalized Montgomery--Taylor kernel and its second
  derivative;
- exhaustive subdivision of every nonnegative six-gap configuration not
  already eliminated by the pressure term;
- certified tangent bounds on convex boxes;
- two rational strong-convexity basins with Hessian lower bound `3/16`;
- zero unresolved terminal cells and checked binary-forest identities.

The canonical 128/256-bit run visits 822,433 nodes.  The 160/320-bit rerun
has the same search counts and independently regenerated interval tables,
though it uses the same implementation and Arb/FLINT library and is therefore
not an independent codebase.

## Files

- `../paper/riemann.tex`: review manuscript source;
- `certificates/seven-point.expected.json`: canonical deterministic report;
- `certificates/seven-point.cross-precision.json`: precision-variant report;
- `docs/proof.md`: exact mathematical deduction;
- `docs/verifier.md`: verifier design and trust base;
- `AUDIT.md`: claim-by-claim audit and open review items;
- `REPRODUCIBILITY.md`: frozen commands and expected output;
- `PROVENANCE.md`: upstream sources, licenses, and modification history.
- `../lean/`: partial Lean formalization; its exact open-boundary ledger is
  `../docs/FORMALIZATION_STATUS.md`.

## Provenance and license

The implementation descends from
[`ainta/zeta-simple-zeros`](https://github.com/ainta/zeta-simple-zeros),
commit `040c5e899e658aed7b56a2a87f501798fe10761d`, and the clean-room release
[`learademacher/ai-refines-ai-zeta-bound`](https://github.com/learademacher/ai-refines-ai-zeta-bound),
commit `bd4a7d36988b23220034527881f4457f2f689e86`.  The inherited code is MIT
licensed.  See `PROVENANCE.md` for the precise scope of the new changes.
