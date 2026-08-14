# Local certificate replay

Date: 2026-08-14

Platform: Linux 6.18.35, x86_64, glibc 2.39

Interpreter: CPython 3.12.13

Interval package: `python-flint==0.8.0`

## Locked dependency

The installed wheel was the hash-locked artifact required by
`verifier/requirements.lock`:

```text
sha256=af60dbed2b0e3bedef2875ff3a2b32afec12f7152595d65fcd674713ac09a208
```

The lock file itself had SHA-256
`c34a96acdd209fde251112c709dc374700b7c28ce18aefc974497910e8d17be7`.

## Unit tests

Command:

```bash
PYTHONPATH=verifier/src /tmp/zeta-seven-venv/bin/python \
  -m unittest discover -s verifier/tests -v
```

Result: all 10 tests passed.

## Canonical certificate

Command:

```bash
PYTHONPATH=verifier/src /tmp/zeta-seven-venv/bin/python \
  verifier/scripts/verify_release.py
```

The final run completed in 105.867 seconds and matched every committed field:

```text
initial_boxes=435
nodes=822433
pruned=411434
splits=410999
maximum_depth=39
interval_pruned=285258
pressure_pruned=2872
tangent_pruned=122329
strong_convexity_pruned=975
unresolved_terminal_cells=0
release_certificate=match
```

## Higher-precision replay

Command:

```bash
PYTHONPATH=verifier/src /tmp/zeta-seven-venv/bin/python \
  verifier/scripts/verify_cross_precision.py
```

The final 160/320-bit run completed in 121.030 seconds with the same logical
counts and ended with:

```text
cross_precision_certificate=match
```

## Separate basin control path

Command:

```bash
/tmp/zeta-seven-venv/bin/python \
  verifier/scripts/verify_basin_independent.py
```

This script does not import the release verifier. It reimplements the kernel
quotient derivatives, subdivides each scalar range into 2,048 exact rational
pieces, and performs the shifted `6 x 6` LDL calculation over exact `fmpq`
arithmetic. Both basins passed. The rigorous lower endpoint was

```text
0.003826231211304474248273717130062706993838230354884912386
```

which is strictly above the exact target
`38262312113/10000000000000`. The script ended with:

```text
independent_basin_certificate=pass
```

This is a separate control path, not a wholly independent interval proof:
both implementations retain Arb/FLINT as their transcendental interval trust
base.
