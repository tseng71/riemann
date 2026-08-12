# Reproducibility guide

## Reference software

```text
python=3.12.x
python-flint=0.8.0
canonical_kernel_precision_bits=128
canonical_basin_precision_bits=256
cross_kernel_precision_bits=160
cross_basin_precision_bits=320
```

The wheel hashes are frozen in `requirements.lock`.  The code relies on
CPython's IEEE-754 binary64 behavior and Arb/FLINT's midpoint-radius interval
arithmetic.

## Local reproduction

```bash
python3.12 -m venv .venv
source .venv/bin/activate
python -m pip install --require-hashes -r requirements.lock
PYTHONPATH=src python -m unittest discover -s tests -v
PYTHONPATH=src python scripts/verify_release.py
```

The last command prints the complete report and ends with:

```text
release_certificate=match
```

Elapsed time is deliberately excluded from the expected JSON comparison.
Every other field must match exactly.

## Canonical deterministic report

```text
verified=true
target=F6 >= 38262312113/10000000000000
grid=4000
precision_bits=128
initial_boxes=435
nodes=822433
pruned=411434
splits=410999
maximum_depth=39
kernel_table_sha256=5a1f95f754a83ba05f37692d4bda69bf3fa5d3752af902826bfc4cffd31428b9
second_derivative_table_sha256=318ee79f619cc75c6f7a30424a181764865910693f33a3d95469ebcae0ce42ba
unresolved_terminal_cells=0
```

The full nested report, including basin bounds and pruning counts, is in
`certificates/seven-point.expected.json`.

## Cross-precision reproduction

```bash
PYTHONPATH=src python scripts/verify_cross_precision.py
```

Expected final line:

```text
cross_precision_certificate=match
```

This run regenerates the tables at 160 bits and the basin calculation at 320
bits.  It has the same 822,433-node search tree.  The second-derivative table
hash changes, as expected for a different interval precision, while every
logical count agrees.  This is a precision stress test, not an independent
implementation.

## Failure semantics

Verification aborts if any of the following occurs:

- a rational basin fails the Arb LDL positive-definiteness check;
- its strong-convexity lower bound does not clear the exact target;
- an exhaustive-search branch reaches an unresolved terminal grid cell;
- the binary-forest identities fail;
- any deterministic report field differs from the committed JSON.

No cached interval table or sampled optimizer output is accepted as evidence.
