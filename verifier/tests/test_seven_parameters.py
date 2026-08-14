import unittest

from zeta_simple_zeros.verify_seven import (
    BASIN_RADIUS,
    BASIN_STRONG_CONVEXITY,
    BASIN_CENTER,
    GRID,
    PRESSURE_CUTOFF_CELLS,
    PRESSURE_DENOMINATOR,
    TARGET_DENOMINATOR,
    TARGET_NUMERATOR,
)


class SevenPointParameterTests(unittest.TestCase):
    def test_strengthened_target(self):
        self.assertEqual(
            (TARGET_NUMERATOR, TARGET_DENOMINATOR),
            (38_262_312_113, 10_000_000_000_000),
        )

    def test_pressure_cutoff_is_derived_from_target(self):
        expected = (
            TARGET_NUMERATOR * GRID * PRESSURE_DENOMINATOR
            + TARGET_DENOMINATOR
            - 1
        ) // TARGET_DENOMINATOR
        self.assertEqual(PRESSURE_CUTOFF_CELLS, expected)
        self.assertEqual(PRESSURE_CUTOFF_CELLS, 45_915)

    def test_strong_convexity_parameters(self):
        self.assertEqual(str(BASIN_RADIUS), "1/64")
        self.assertEqual(str(BASIN_STRONG_CONVEXITY), "3/16")
        self.assertEqual(len(BASIN_CENTER), 6)
        self.assertEqual(str(BASIN_CENTER[0]), "104608035577/100000000000")


if __name__ == "__main__":
    unittest.main()
