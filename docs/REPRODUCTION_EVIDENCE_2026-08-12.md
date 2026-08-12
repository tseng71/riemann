# Reproduction evidence — 2026-08-12

This record describes a clean replay performed while preparing the public
review branch.  It is evidence about the committed implementation, not an
independent implementation and not a Lean proof term.

## Environment

```text
Python 3.12.13
python-flint 0.8.0
Linux 6.18.35 x86_64
```

## Results

| Check | Result |
| --- | --- |
| Python unit tests | 10 passed |
| Canonical 128/256-bit replay | `release_certificate=match` |
| Cross 160/320-bit replay | `cross_precision_certificate=match` |
| Canonical nodes / unresolved | 822,433 / 0 |
| Cross-precision nodes / unresolved | 822,433 / 0 |
| Splits / pruned / maximum depth | 410,999 / 411,434 / 39 |
| Lean `lake build ZetaSeven` | 8,846 jobs completed |
| Lean source placeholder scan | clean |
| Lean axiom audit | `propext`, `Classical.choice`, `Quot.sound` only |

Canonical elapsed time was approximately 343.3 seconds; the cross-precision
replay took approximately 345.2 seconds.  Elapsed time is intentionally not
part of the deterministic certificate comparison.

## Committed report hashes

```text
703f634a34b27ed2545cf45a23f88ad409f0a087be11b0703a164bece2537319  seven-point.expected.json
ed5000fcfa49c739e9f103794f12aa884055942bd7c70bd9c80784fa5901efc3  seven-point.cross-precision.json
```

The canonical regenerated kernel and second-derivative table hashes are

```text
5a1f95f754a83ba05f37692d4bda69bf3fa5d3752af902826bfc4cffd31428b9
318ee79f619cc75c6f7a30424a181764865910693f33a3d95469ebcae0ce42ba
```

At 160 bits the kernel hash is unchanged and the regenerated
second-derivative table hash is

```text
fd634c87441380105aad52f069f735108d0dabcd7d5d0a993b6abc52ee12b055
```
