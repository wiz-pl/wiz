#!/usr/bin/env python3
"""Tests for the independent third checker (run: `python3 -m unittest -v` here).

The positive/negative corpus is the *kernel-level* corpus in `driver.py`; the verdicts
come from `corpus.dump`, produced by the self-hosted kernel.  These tests check the
checker against that dump and exercise the four required cases directly, so they also
run when the dump is absent (the dump agreement test is then skipped).
"""

import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import checker  # noqa: E402
import driver   # noqa: E402

DUMP = os.path.join(HERE, "corpus.dump")


def load_dump():
    with open(DUMP) as f:
        return f.read()


def decl(name):
    for n, ty, val, _ in driver.DECLS:
        if n == name:
            return ty, val
    raise KeyError(name)


class TestFormat(unittest.TestCase):
    def test_roundtrip(self):
        for name, ty, val, _ in driver.DECLS:
            for t in (ty, val):
                text = driver.ser(t)
                got = checker.parse_term(checker.parse_sexpr(checker.tokenize(text)))
                self.assertEqual(got, t, f"{name}: {text}")

    def test_dump_uses_the_same_format(self):
        """The Wiz serializer (which produced the dump) and driver.ser agree."""
        if not os.path.exists(DUMP):
            self.skipTest("no corpus.dump (run harness.py --regen)")
        for verdict, name, ty_s, val_s in checker.read_dump(load_dump()):
            for t, s in ((decl(name)[0], ty_s), (decl(name)[1], val_s)):
                self.assertEqual(driver.ser(t), s, name)


class TestRequiredCases(unittest.TestCase):
    def test_positive_terms(self):
        if not os.path.exists(DUMP):
            self.skipTest("no corpus.dump (run harness.py --regen)")
        ok = 0
        for verdict, name, ty_s, val_s in checker.read_dump(load_dump()):
            if verdict != "OK":
                continue
            ty = checker.parse_term(checker.parse_sexpr(checker.tokenize(ty_s)))
            val = checker.parse_term(checker.parse_sexpr(checker.tokenize(val_s)))
            good, msg = checker.check_decl(ty, val)
            self.assertTrue(good, f"{name}: {msg}")
            ok += 1
        self.assertGreaterEqual(ok, 20, "the corpus must have at least 20 positives")

    def test_ill_typed_proof(self):
        ty, val = decl("bad-proof")
        good, _ = checker.check_decl(ty, val)
        self.assertFalse(good)

    def test_wrong_level(self):
        ty, val = decl("bad-level")
        good, _ = checker.check_decl(ty, val)
        self.assertFalse(good)

    def test_quantity_violations(self):
        for name in ("bad-linear-dup", "bad-linear-drop"):
            ty, val = decl(name)
            good, msg = checker.check_decl(ty, val)
            self.assertFalse(good, name)
            self.assertIn("quantity", msg, name)

    def test_linear_control_is_accepted(self):
        ty, val = decl("linear-ok")
        good, msg = checker.check_decl(ty, val)
        self.assertTrue(good, msg)


class TestCheckerIndependently(unittest.TestCase):
    """Cases built here, not taken from the kernel's verdicts."""

    def test_tampered_identity_is_rejected(self):
        ty, _ = decl("id")
        bad = driver.LAM(driver.LAM(driver.STAR))
        good, _ = checker.check_decl(ty, bad)
        self.assertFalse(good)

    def test_true_equations_are_convertible(self):
        # both reduce to True (`vEq` at an enumeration), so the kernel accepts the
        # first too; an independent checker must not be stricter than the rules
        for tag in (0, 1):
            ty = driver.EQ(driver.ENUM(2), driver.TAG(2, tag), driver.TAG(2, tag))
            val = driver.REFL(driver.ENUM(2), driver.TAG(2, tag))
            good, msg = checker.check_decl(ty, val)
            self.assertTrue(good, msg)

    def test_true_against_false_equality_is_rejected(self):
        ty = driver.EQ(driver.ENUM(2), driver.TAG(2, 0), driver.TAG(2, 1))
        val = driver.REFL(driver.ENUM(2), driver.TAG(2, 0))
        good, _ = checker.check_decl(ty, val)
        self.assertFalse(good)

    def test_unsupported_rule_is_rejected_not_accepted(self):
        # `ind` is out of scope; the checker must not silently accept it
        ty = driver.UNIT(0)
        val = driver.IND(0, driver.UNIT(0), driver.DRET(driver.STAR), 0,
                         driver.LAM(driver.UNIT(0)), driver.STAR, driver.STAR, driver.STAR)
        good, msg = checker.check_decl(ty, val)
        self.assertFalse(good)
        self.assertIn("out of scope", msg)


if __name__ == "__main__":
    unittest.main()
