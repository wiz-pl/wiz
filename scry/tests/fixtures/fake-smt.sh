#!/bin/sh
# A deterministic stand-in for an SMT solver, used by tests/smt.wiz. It answers
# `--version` for Scry.Smt.probe, then prints the answer named by its first argument.
# The real path (`Scry.Smt.defaultSolver`) is still z3; this fixture only makes the
# process/parse/validate plumbing testable without a solver on the machine.
case "$1" in
  --version) echo "fake-smt 1.0"; exit 0 ;;
  unsat) echo unsat; exit 0 ;;
  unknown) echo unknown; exit 0 ;;
  sat-bad) echo sat; echo "((len"; echo "20))"; exit 0 ;;
  sat) echo sat; echo "((len"; echo "3))"; exit 0 ;;
  *) echo "fake-smt: unknown answer '$1'" >&2; exit 2 ;;
esac
