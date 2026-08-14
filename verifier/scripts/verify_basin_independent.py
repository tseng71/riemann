#!/usr/bin/env python3
"""Independent audit of the two strong-convexity basin certificates.

This script deliberately does not import the release verifier.  It rebuilds
the kernel jet from the quotient formulas, encloses each scalar Hessian term
on a fresh rational subdivision, and performs the 6 x 6 LDL test over exact
``fmpq`` arithmetic.  Arb is still the transcendental interval backend.
"""

from __future__ import annotations

import math

from flint import arb, ctx, fmpq


BITS = 256
SUBDIVISIONS = 2048
RADIUS = fmpq(1, 64)
MU = fmpq(3, 16)
TARGET = fmpq(38_262_312_113, 10_000_000_000_000)
CENTER = (
    fmpq(104_608_035_577, 100_000_000_000),
    fmpq(198_913_202_062, 100_000_000_000),
    fmpq(198_641_493_611, 100_000_000_000),
    fmpq(104_160_329_372, 100_000_000_000),
    fmpq(197_702_352_234, 100_000_000_000),
    fmpq(104_500_209_462, 100_000_000_000),
)


def exact_ball(left: fmpq, right: fmpq) -> arb:
    return arb((left + right) / 2, (right - left) / 2)


def downward_dyadic(value: arb) -> fmpq:
    """Return an exact binary64 rational strictly below an Arb lower end."""

    candidate = math.nextafter(float(value.lower()), -math.inf)
    if not math.isfinite(candidate):
        raise RuntimeError("non-finite lower endpoint")
    numerator, denominator = candidate.as_integer_ratio()
    return fmpq(numerator, denominator)


def kernel_jet(x: arb) -> tuple[arb, arb, arb]:
    """Return w, w', w'' directly from sin(z)/z quotient formulas."""

    sqrt_two = arb(2).sqrt()
    inv_sqrt_two = 1 / sqrt_two
    pi = arb.pi()
    normalization = sqrt_two * inv_sqrt_two.sin()

    def sinc_jet(z: arb) -> tuple[arb, arb, arb]:
        sine = z.sin()
        cosine = z.cos()
        z2 = z * z
        return (
            sine / z,
            (z * cosine - sine) / z2,
            ((2 - z2) * sine - 2 * z * cosine) / (z2 * z),
        )

    left = sinc_jet(pi * x - inv_sqrt_two)
    right = sinc_jet(pi * x + inv_sqrt_two)
    raw = (left[0] + right[0]) / 2
    raw_prime = pi * (left[1] + right[1]) / 2
    raw_second = pi * pi * (left[2] + right[2]) / 2
    norm2 = normalization * normalization
    value = raw * raw / norm2
    first = 2 * raw * raw_prime / norm2
    second = 2 * (raw_prime * raw_prime + raw * raw_second) / norm2
    return value, first, second


def scalar_second_lower(left: fmpq, right: fmpq) -> fmpq:
    """Enclose w'' over [left,right] using a fresh uniform subdivision."""

    width = (right - left) / SUBDIVISIONS
    result: fmpq | None = None
    for index in range(SUBDIVISIONS):
        cell_left = left + index * width
        cell_right = cell_left + width
        second = kernel_jet(exact_ball(cell_left, cell_right))[2]
        lower = downward_dyadic(second)
        if result is None or lower < result:
            result = lower
    assert result is not None
    return result


def exact_ldl_positive(matrix: list[list[fmpq]]) -> tuple[bool, list[fmpq]]:
    """Exact no-pivot LDL; positivity of all pivots is equivalent to PD."""

    lower = [[fmpq(0) for _ in range(6)] for _ in range(6)]
    diagonal = [fmpq(0) for _ in range(6)]
    for column in range(6):
        lower[column][column] = fmpq(1)
        pivot = matrix[column][column]
        for previous in range(column):
            pivot -= lower[column][previous] ** 2 * diagonal[previous]
        if pivot <= 0:
            return False, diagonal + [pivot]
        diagonal[column] = pivot
        for row in range(column + 1, 6):
            entry = matrix[row][column]
            for previous in range(column):
                entry -= (
                    lower[row][previous]
                    * lower[column][previous]
                    * diagonal[previous]
                )
            lower[row][column] = entry / pivot
    return True, diagonal


def check_center(center: tuple[fmpq, ...]) -> None:
    matrix = [[fmpq(0) for _ in range(6)] for _ in range(6)]
    for span in range(1, 7):
        coefficient = fmpq(2, 7 - span)
        for start in range(7 - span):
            midpoint = sum(center[start : start + span], fmpq(0))
            left = midpoint - span * RADIUS
            right = midpoint + span * RADIUS
            scalar = coefficient * scalar_second_lower(left, right)
            for row in range(start, start + span):
                for column in range(start, start + span):
                    matrix[row][column] += scalar

    shifted = [row[:] for row in matrix]
    for index in range(6):
        shifted[index][index] -= MU
    positive, pivots = exact_ldl_positive(shifted)
    if not positive:
        raise RuntimeError("exact LDL failed")

    gaps = [arb(point) for point in center]
    value = sum(gaps, arb(0)) / 3000
    gradient = [arb(fmpq(1, 3000)) for _ in range(6)]
    for span in range(1, 7):
        coefficient = arb(fmpq(2, 7 - span))
        for start in range(7 - span):
            point = sum(gaps[start : start + span], arb(0))
            potential, derivative, _ = kernel_jet(point)
            value += coefficient * potential
            for coordinate in range(start, start + span):
                gradient[coordinate] += coefficient * derivative

    correction = arb(0)
    for derivative in gradient:
        upper = derivative.abs_upper()
        correction += upper * upper / (2 * arb(MU))
    lower_bound = value - correction
    if not (lower_bound > arb(TARGET)):
        raise RuntimeError("independent basin value does not clear target")

    print("center=" + ",".join(str(point) for point in center))
    print("minimum_exact_ldl_pivot=" + str(min(pivots)))
    print("basin_lower=" + lower_bound.lower().str(55, radius=False))
    print("target=" + str(TARGET))


def main() -> None:
    ctx.prec = BITS
    check_center(CENTER)
    check_center(tuple(reversed(CENTER)))
    print("independent_basin_certificate=pass")


if __name__ == "__main__":
    main()
