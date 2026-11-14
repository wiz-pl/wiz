#!/usr/bin/env python3
"""Tests for the independent third checker (run: `python3 -m unittest -v` here).

The positive/negative corpus is the *kernel-level* corpus in `driver.py`; the verdicts
come from `corpus.dump`, produced by the self-hosted kernel.  These tests check the
checker against that dump and exercise the rules the kernel's fragment cannot express
(`split`) plus the mismatch detector, so they also run when the dump is absent (the
dump agreement test is then skipped).
"""

import contextlib
import io
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import checker  # noqa: E402
import driver   # noqa: E402
import harness  # noqa: E402

DUMP = os.path.join(HERE, "corpus.dump")

NEGATIVES = ("bad-proof", "bad-level", "bad-eq-prop",
             "bad-linear-dup", "bad-linear-drop")


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


class TestCorpusVerdicts(unittest.TestCase):
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
        self.assertGreaterEqual(ok, 40, "the corpus must have at least 40 positives")

    def test_negative_terms(self):
        if not os.path.exists(DUMP):
            self.skipTest("no corpus.dump (run harness.py --regen)")
        for verdict, name, ty_s, val_s in checker.read_dump(load_dump()):
            if verdict != "ERR":
                continue
            ty = checker.parse_term(checker.parse_sexpr(checker.tokenize(ty_s)))
            val = checker.parse_term(checker.parse_sexpr(checker.tokenize(val_s)))
            good, msg = checker.check_decl(ty, val)
            self.assertFalse(good, f"{name} was accepted: {msg}")
        self.assertGreaterEqual(len(NEGATIVES), 5)

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

    def test_new_inductive_rules_are_present(self):
        for name in ("nat-type", "nat-zero", "nat-succ", "nat-ind",
                     "list-type", "list-nil", "list-cons", "desc-elim"):
            ty, val = decl(name)
            good, msg = checker.check_decl(ty, val)
            self.assertTrue(good, f"{name}: {msg}")

    def test_level_parameters_are_present(self):
        for name in ("level-param-sort", "level-param-max",
                     "level-param-id", "level-param-const"):
            ty, val = decl(name)
            good, msg = checker.check_decl(ty, val)
            self.assertTrue(good, f"{name}: {msg}")


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
        # sizes/coinduction are out of scope; the checker must not silently accept them
        ty = driver.UNIT(0)
        val = ("out", driver.CON(driver.STAR))
        good, msg = checker.check_decl(ty, val)
        self.assertFalse(good)
        self.assertIn("out of scope", msg)

    def test_induction_method_type_is_checked(self):
        # a method that returns a tag of the wrong enumeration is ill typed
        bad_m = driver.LAM(driver.LAM(driver.LAM(driver.TAG(3, 0))))
        val = driver.LAM(driver.IND(
            0, driver.UNIT(0), driver.NAT_D, 1,
            driver.LAM(driver.LAM(driver.ENUM(2))), bad_m,
            driver.STAR, driver.V(0)))
        good, _ = checker.check_decl(decl("nat-ind")[0], val)
        self.assertFalse(good)

    def test_delim_on_a_non_description_is_rejected(self):
        val = driver.LAM(driver.DELIM(
            1, driver.LAM(driver.ENUM(2)), driver.LAM(driver.TAG(2, 0)),
            driver.LAM(driver.LAM(driver.LAM(driver.LAM(driver.TAG(2, 1))))),
            driver.LAM(driver.LAM(driver.LAM(driver.LAM(driver.TAG(2, 1))))),
            driver.LAM(driver.LAM(driver.LAM(driver.LAM(driver.LAM(driver.TAG(2, 1)))))),
            driver.UNIT(0)))
        good, msg = checker.check_decl(decl("desc-elim")[0], val)
        self.assertFalse(good)
        self.assertIn("description", msg)


class TestQuantityCases(unittest.TestCase):
    def _sig(self, q):
        return driver.SIG(q, driver.N(1), driver.N(1), driver.UNIT(0), driver.UNIT(0))

    def test_linear_projection_is_rejected(self):
        ty = driver.PI(driver.Q1, driver.N(1), driver.N(1),
                       self._sig(driver.Q1), driver.UNIT(0))
        good, msg = checker.check_decl(ty, driver.LAM(driver.FST(driver.V(0))))
        self.assertFalse(good)
        self.assertIn("quantity", msg)

    def test_erased_field_projection_is_rejected(self):
        ty = driver.PI(driver.QW, driver.N(1), driver.N(1),
                       self._sig(driver.Q0), driver.UNIT(0))
        good, msg = checker.check_decl(ty, driver.LAM(driver.FST(driver.V(0))))
        self.assertFalse(good)
        self.assertIn("erased field", msg)

    def test_unrestricted_projection_is_accepted(self):
        ty = driver.PI(driver.QW, driver.N(1), driver.N(1),
                       self._sig(driver.QW), driver.UNIT(0))
        good, msg = checker.check_decl(ty, driver.LAM(driver.FST(driver.V(0))))
        self.assertTrue(good, msg)

    def test_linear_let_used_twice_is_rejected(self):
        end = driver.ANN(driver.STAR, driver.UNIT(0))
        body = driver.LETUNIT(driver.V(0), driver.LETUNIT(driver.V(0), end))
        val = driver.LAM(driver.LETQ(driver.Q1, driver.UNIT(0), driver.V(0), body))
        ty = driver.PI(driver.Q1, driver.N(1), driver.N(1),
                       driver.UNIT(0), driver.UNIT(0))
        good, msg = checker.check_decl(ty, val)
        self.assertFalse(good)
        self.assertIn("let-bound", msg)


class TestSplit(unittest.TestCase):
    """`split` is in CoreSpec but not in Kernel.wiz's term language, so it has no
    corpus declaration; these cases exercise the checker's rule directly."""

    def _sig(self, q):
        return driver.SIG(q, driver.N(1), driver.N(1), driver.UNIT(0), driver.UNIT(0))

    def test_split_at_omega_is_checked(self):
        val = ("split", driver.QW,
               driver.ANN(driver.PAIR(driver.STAR, driver.STAR), self._sig(driver.QW)),
               driver.UNIT(0), driver.STAR)
        good, msg = checker.check_decl(driver.UNIT(0), val)
        self.assertTrue(good, msg)

    def test_linear_split_using_both_components(self):
        body = driver.LETUNIT(driver.V(1), driver.LETUNIT(driver.V(0), driver.STAR))
        val = driver.LAM(("split", driver.Q1, driver.V(0),
                          driver.UNIT(0), body))
        ty = driver.PI(driver.Q1, driver.N(1), driver.N(1),
                       self._sig(driver.Q1), driver.UNIT(0))
        good, msg = checker.check_decl(ty, val)
        self.assertTrue(good, msg)

    def test_linear_split_dropping_a_component_is_rejected(self):
        body = driver.LETUNIT(driver.V(1), driver.STAR)  # drops y
        val = driver.LAM(("split", driver.Q1, driver.V(0),
                          driver.UNIT(0), body))
        ty = driver.PI(driver.Q1, driver.N(1), driver.N(1),
                       self._sig(driver.Q1), driver.UNIT(0))
        good, msg = checker.check_decl(ty, val)
        self.assertFalse(good)
        self.assertIn("quantity", msg)

    def test_linear_split_using_a_component_twice_is_rejected(self):
        body = driver.LETUNIT(driver.V(1), driver.LETUNIT(driver.V(1), driver.STAR))
        val = driver.LAM(("split", driver.Q1, driver.V(0),
                          driver.UNIT(0), body))
        ty = driver.PI(driver.Q1, driver.N(1), driver.N(1),
                       self._sig(driver.Q1), driver.UNIT(0))
        good, msg = checker.check_decl(ty, val)
        self.assertFalse(good)
        self.assertIn("quantity", msg)

    def test_split_on_a_pair_computes(self):
        t = ("split", driver.QW,
             driver.ANN(driver.PAIR(driver.STAR, driver.STAR), self._sig(driver.QW)),
             driver.UNIT(0), driver.V(1))
        self.assertEqual(checker.whnf(t), driver.STAR)


class TestLevels(unittest.TestCase):
    def test_imax_with_a_parameter(self):
        u = driver.P("u")
        self.assertTrue(checker.level_eq(driver.IMAX(u, u), u))
        self.assertTrue(checker.level_eq(driver.IMAX(u, driver.N(0)), driver.N(0)))

    def test_imax_with_a_parameter_that_matters(self):
        u = driver.P("u")
        self.assertFalse(checker.level_eq(driver.IMAX(driver.N(1), u), driver.N(1)))

    def test_const_levels_are_instantiated(self):
        u = driver.P("u")
        ty = driver.PI(driver.Q0, driver.SUC(u), u, driver.SL(u),
                       driver.PI(driver.Q1, u, u, driver.V(0), driver.V(1)))
        inst = checker.inst_levels(ty, ("u",), (driver.N(1),))
        self.assertTrue(checker.level_eq(inst[2], driver.N(2)))
        self.assertTrue(checker.level_eq(inst[3], driver.N(1)))
        self.assertEqual(inst[4], driver.SL(driver.N(1)))
        self.assertTrue(checker.level_eq(inst[5][2], driver.N(1)))
        self.assertTrue(checker.level_eq(inst[5][3], driver.N(1)))


class TestMismatch(unittest.TestCase):
    def test_a_forged_ok_is_a_mismatch(self):
        # the checker, not the verdict column, decides this term is ill typed
        ty, val = decl("bad-proof")
        line = "OK\tbad-proof\t" + driver.ser(ty) + "\t" + driver.ser(val)
        rows = checker.check_dump(line)
        self.assertEqual(len(rows), 1)
        verdict, name, ok, msg = rows[0]
        self.assertEqual((verdict, name), ("OK", "bad-proof"))
        self.assertFalse(ok, msg)
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            bad = harness.report(rows, False)
        self.assertEqual(bad, 1)
        self.assertIn("1 mismatches", buf.getvalue())

    def test_a_forged_err_is_a_mismatch(self):
        ty, val = decl("id")
        line = "ERR\tid\t" + driver.ser(ty) + "\t" + driver.ser(val)
        rows = checker.check_dump(line)
        self.assertTrue(rows[0][2])
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            bad = harness.report(rows, False)
        self.assertEqual(bad, 1)


if __name__ == "__main__":
    unittest.main()
