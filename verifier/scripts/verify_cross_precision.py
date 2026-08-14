#!/usr/bin/env python3
"""Rebuild the seven-point certificate at higher Arb precisions."""

from __future__ import annotations

import json
from dataclasses import asdict
from pathlib import Path

import zeta_simple_zeros.verify_seven as seven


ROOT = Path(__file__).resolve().parents[1]
EXPECTED_PATH = ROOT / "certificates" / "seven-point.cross-precision.json"


def main() -> int:
    seven.PRECISION_BITS = 160
    seven.BASIN_PRECISION_BITS = 320
    expected = json.loads(EXPECTED_PATH.read_text(encoding="utf-8"))
    actual = asdict(seven.verify_seven())
    elapsed_seconds = actual.pop("elapsed_seconds")

    print(
        json.dumps(
            {**actual, "elapsed_seconds": elapsed_seconds},
            indent=2,
            sort_keys=True,
        )
    )
    if actual != expected:
        print("cross_precision_certificate=mismatch")
        for key in sorted(set(expected) | set(actual)):
            if expected.get(key) != actual.get(key):
                print(
                    f"field={key} expected={expected.get(key)!r} "
                    f"actual={actual.get(key)!r}"
                )
        return 1

    print("cross_precision_certificate=match")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
