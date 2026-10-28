#!/usr/bin/env python3
"""Registered finite source consumers, mutations and exact full-path checks."""
import copy
from fractions import Fraction as Q
import unittest

from exact_certificates import (Source, candidate_weights, check_negative, check_positive,
                                derive, path_law, registered_cases, run, verify_path_identity)


class Certificates(unittest.TestCase):
    def test_registered_sources(self):
        cases = registered_cases()
        expected = {
            "original_actions": "CANDIDATE_UNREALIZABLE",
            "two_step_added_actions": "CANDIDATE_REALIZABLE",
            "unprepared_initial": "CANDIDATE_UNREALIZABLE",
            "same_source_alias": "CANDIDATE_UNREALIZABLE",
            "unreachable_fallback": "CANDIDATE_REALIZABLE",
            "independent_baseline_variant": "CANDIDATE_REALIZABLE",
            "zero_horizon": "CANDIDATE_REALIZABLE",
            "zero_survival": "CONDITIONING_UNDEFINED",
        }
        self.assertEqual({k: run(v)["status"] for k, v in cases.items()}, expected)
        r = run(cases["two_step_added_actions"])
        self.assertEqual(r["target"]["Z"], Q(1, 4))
        self.assertEqual(r["target"]["mu"], (Q(3, 4), Q(1, 4), 0))
        self.assertEqual(r["certificate"]["weights"], [[(0, Q(3, 4), Q(1, 4))], [(0, Q(1, 2), Q(1, 2))]])
        law = path_law(r["target"]["mu"], r["target"]["R"], 2)
        self.assertEqual(list(law.values()), [Q(x, 32) for x in (9, 9, 3, 3, 3, 3, 1, 1)])
        self.assertEqual(run(cases["unprepared_initial"])["initial_TV_lower_bound"], Q(1, 4))
        variant = run(cases["independent_baseline_variant"])
        self.assertEqual(variant["certificate"]["weights"], [[(0, Q(1, 3), Q(2, 3))]] * 2)

    def test_same_source_alias_and_certificate_rejection(self):
        raw = registered_cases()["same_source_alias"]
        s, result = Source.read(raw), run(raw)
        d, c = result["target"], result["certificate"]
        self.assertEqual(d["Z"], Q(1, 2))
        self.assertTrue(check_negative(s, c))
        # Each hidden-state target row is individually realizable. They cannot
        # use separate weights when the observation is constant.
        self.assertEqual(d["R"][0][0], (1, 0, 0))
        self.assertEqual(d["R"][0][1], (0, 1, 0))
        for key, value in [("gap", 0), ("bound", c["bound"] + 100), ("time", 1), ("source", "wrong"),
                           ("observation", 1), ("coefficient", [[0] * 3] * 3)]:
            self.assertFalse(check_negative(s, {**c, key: value}), key)
        wrong = {"source": s.identity, "weights": [[(Q(1, 2), Q(1, 2))]]}
        self.assertFalse(check_positive(s, wrong))

    def test_positive_rejection_and_unoccupied_row(self):
        raw = registered_cases()["unreachable_fallback"]
        s, r = Source.read(raw), run(raw)
        d, c = r["target"], r["certificate"]
        self.assertTrue(check_positive(s, c))
        self.assertTrue(verify_path_identity(s, d, c))
        self.assertTrue(all(v[2] == 0 for v in d["occupancy"]))
        self.assertEqual(d["R"][0][2], (0, 0, 1))
        self.assertTrue(all(row[2] == 0 for row in s.P[2]))
        for weights in [[[(1, 0, 0)]] * 2, [[(0, Q(3, 4), Q(1, 4))]] * 2,
                        [[(-1, 1, 1)]] * 2, [[(0, 1, 1)]] * 2, []]:
            self.assertFalse(check_positive(s, {**c, "weights": weights}))
        self.assertFalse(check_positive(s, {**c, "source": "wrong"}))

    def test_input_boundary(self):
        raw = registered_cases()["two_step_added_actions"]
        for field, val in [("T", -1), ("T", True), ("q", [0, 0, 2]), ("safe", [1, 1, 0]),
                           ("deployed", [0.75, 0.25, 0]), ("p0", [1, 1, 0]), ("P", [])]:
            self.assertEqual(run({**raw, field: val})["status"], "INVALID_INPUT", field)
        altered = copy.deepcopy(raw)
        altered["P"][0][0][0] = "-1/8"
        self.assertEqual(run(altered)["status"], "INVALID_INPUT")


if __name__ == "__main__":
    unittest.main()
