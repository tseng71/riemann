"""Run the exhaustive certificate and check every deterministic release field."""

from __future__ import annotations

import json
from dataclasses import asdict
from pathlib import Path

from zeta_simple_zeros.verify_seven import verify_seven


ROOT = Path(__file__).resolve().parents[1]
EXPECTED_PATH = ROOT / "certificates" / "seven-point.expected.json"


def main() -> int:
    expected = json.loads(EXPECTED_PATH.read_text(encoding="utf-8"))
    actual = asdict(verify_seven())
    elapsed_seconds = actual.pop("elapsed_seconds")

    print(json.dumps({**actual, "elapsed_seconds": elapsed_seconds}, indent=2, sort_keys=True))
    if actual != expected:
        print("release certificate mismatch")
        for key in sorted(set(expected) | set(actual)):
            if expected.get(key) != actual.get(key):
                print(
                    f"field={key} expected={expected.get(key)!r} actual={actual.get(key)!r}"
                )
        return 1

    print("release_certificate=match")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
