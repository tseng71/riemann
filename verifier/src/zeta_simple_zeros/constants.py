"""Closed-form constants occurring in the two certificates."""

from __future__ import annotations

import math


H0 = 1.5 - (1.0 / math.sqrt(2.0)) / math.tan(1.0 / math.sqrt(2.0))
"""Anthropic's Montgomery-Taylor constant (Theorem D)."""


def three_point_bound(epsilon: float) -> float:
    """Return (H0 - epsilon/4) / (1 - epsilon/2)."""

    if not 0.0 < epsilon <= 1.0:
        raise ValueError("epsilon must lie in (0, 1]")
    return (H0 - epsilon / 4.0) / (1.0 - epsilon / 2.0)


def seven_point_bound() -> float:
    """Return the bound produced by the certified F6 >= 0.0038262312113.

    The block size 267 is optimal for this local constant in the shifted
    block argument.  At that size C*(m-6) is still below one; at m=268 the
    block-defect cap becomes active and the resulting global bound decreases.
    """

    local_constant = 38_262_312_113.0 / 10_000_000_000_000.0
    block_size = 267.0
    return (
        block_size * H0 - (block_size - 1.0) / 500.0
    ) / (
        block_size - local_constant * (block_size - 6.0)
    )
