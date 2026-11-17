"""Tests for the library index (search, doc) and the read-only resources (P2a)."""

from __future__ import annotations

import json
import os
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

import wiz_index  # noqa: E402
import wiz_mcp  # noqa: E402

PRELUDE = '''/-! # Prelude

The basics. -/

/-- The natural numbers. -/
inductive Nat where
  | zero
  | succ (n : Nat)

/-- Addition: `Nat.add 2 3 = 5`.

More text. -/
def Nat.add : Nat → Nat → Nat
  | .zero, n => n
  | .succ m, n => .succ (Nat.add m n)

/- an ordinary comment
def Hidden.inComment : Nat := 0
-/

-- not a doc
def Nat.double (n : Nat) : Nat := Nat.add n n

inductive List (A : Type) where
  | nil
  | cons (head : A) (tail : List A)

/-- Apply `f` to every element. -/
def List.map {A B : Type} (f : A → B) : List A → List B
  | .nil => .nil
  | .cons x xs => .cons (f x) (List.map f xs)

def List.length {A : Type} : List A → Nat
  | .nil => .zero
  | .cons _ xs => .succ (List.length xs)

/-- A default value. -/
class Inhabited.{u} (A : Type u) where
  /-- the value -/
  default : A

structure Point where
  x : Nat
  y : Nat

instance : Inhabited Nat := Inhabited.mk .zero

@[simp] partial def loop (n : Nat) : Nat := loop n

extern "wiz_print" printNat : Nat → Nat

axiom Classical.choice {A : Type} : A
'''


class ScanTests(unittest.TestCase):
    def setUp(self) -> None:
        self.doc, decls = wiz_index.scan_source(PRELUDE, "Prelude", "/lib/Prelude.wiz")
        self.by = {d.name: d for d in decls}

    def test_module_doc(self) -> None:
        self.assertTrue(self.doc.startswith("# Prelude"))

    def test_declarations_and_kinds(self) -> None:
        kinds = {n: d.kind for n, d in self.by.items()}
        self.assertEqual(kinds["Nat"], "inductive")
        self.assertEqual(kinds["Nat.add"], "def")
        self.assertEqual(kinds["Nat.succ"], "constructor")
        self.assertEqual(kinds["Inhabited"], "class")
        self.assertEqual(kinds["Inhabited.default"], "field")
        self.assertEqual(kinds["Point.y"], "field")
        self.assertEqual(kinds["loop"], "def")
        self.assertEqual(kinds["printNat"], "extern")
        self.assertEqual(kinds["Classical.choice"], "axiom")
        self.assertNotIn("Hidden.inComment", self.by)

    def test_docs_attach_to_the_next_declaration_only(self) -> None:
        self.assertTrue(self.by["Nat.add"].doc.startswith("Addition"))
        self.assertEqual(self.by["Nat.double"].doc, "")
        self.assertEqual(self.by["Inhabited.default"].doc, "the value")
        self.assertEqual(wiz_index.summary(self.by["Nat.add"].doc), "Addition: `Nat.add 2 3 = 5`.")

    def test_lines_are_one_based(self) -> None:
        self.assertEqual(PRELUDE.split("\n")[self.by["Nat.add"].line - 1][:11], "def Nat.add")

    def test_arrow_types(self) -> None:
        arrow = lambda n: wiz_index.arrow_type(self.by[n].sig)  # noqa: E731
        self.assertEqual(arrow("Nat.add"), "Nat → Nat → Nat")
        self.assertEqual(arrow("Nat.double"), "Nat → Nat")
        self.assertEqual(arrow("List.map"), "(A → B) → List A → List B")
        self.assertEqual(arrow("Nat.succ"), "Nat → Nat")
        self.assertEqual(arrow("List.cons"), "A → List A → List A")
        self.assertEqual(arrow("printNat"), "Nat → Nat")
        self.assertEqual(arrow("Classical.choice"), "A")


class TypeScoreTests(unittest.TestCase):
    def test_exact_variables_order_suffix(self) -> None:
        self.assertEqual(wiz_index.type_score("Nat → Nat → Nat", "Nat → Nat → Nat"), 100)
        self.assertEqual(wiz_index.type_score("(α → β) → List α → List β", "(A → B) → List A → List B"), 80)
        self.assertEqual(wiz_index.type_score("List _ → Nat", "List A → Nat"), 80)
        self.assertEqual(wiz_index.type_score("Bool → Nat → Nat", "Nat → Bool → Nat"), 60)
        self.assertEqual(wiz_index.type_score("Nat → Nat", "Bool → Nat → Nat"), 40)
        self.assertEqual(wiz_index.type_score("α → α", "Nat → Bool"), 0)
        self.assertEqual(wiz_index.type_score("String", "Nat → Nat"), 0)


def make_toolchain(root: str) -> tuple[str, str]:
    """A fake installed toolchain: PREFIX/bin/wiz and PREFIX/share/wiz/lib/*.wiz."""
    prefix = os.path.join(root, "prefix")
    os.makedirs(os.path.join(prefix, "bin"))
    lib = os.path.join(prefix, "share", "wiz", "lib")
    os.makedirs(os.path.join(lib, "Data"))
    Path(lib, "Prelude.wiz").write_text(PRELUDE)
    Path(lib, "Data", "Extra.wiz").write_text("/-- Twice. -/\ndef Extra.twice (n : Nat) : Nat := n\n")
    wiz = os.path.join(prefix, "bin", "wiz")
    Path(wiz).write_text("#!/bin/sh\necho wiz\n")
    os.chmod(wiz, 0o755)
    return wiz, lib


class ServerTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory(prefix="wiz-mcp-index-")
        self.wiz, self.lib = make_toolchain(self.tmp.name)
        self.workspace = os.path.join(self.tmp.name, "ws")
        os.makedirs(os.path.join(self.workspace, "docs", "stages"))
        os.makedirs(os.path.join(self.workspace, ".github"))
        os.makedirs(os.path.join(self.workspace, ".lake"))
        Path(self.workspace, "Mine.wiz").write_text("def Mine.go (b : Bool) : Nat := 0\n")
        Path(self.workspace, ".lake", "Built.wiz").write_text("def Built.skip : Nat := 0\n")
        Path(self.workspace, ".github", "trust-baseline.tsv").write_text(
            "# header\nPrelude\tClassical.choice\taxiom\tchoice\tkernel\t2026-11\n"
            "Text\tprintNat\textern\tFFI\truntime\t2026-11\n")
        Path(self.workspace, "docs", "error-codes.md").write_text(
            "# Error codes\n\n| code | the error | example | quick fixes |\n|---|---|---|---|\n"
            "| `unknown-identifier` | a name not in scope | `doubel 2` | did you mean |\n"
            "| `type-mismatch` | types differ | `x \\| y` | |\n")
        Path(self.workspace, "docs", "stages", "01-kernel.md").write_text("# Stage 1: the kernel\n\ntext\n")
        Path(self.tmp.name, "secret.md").write_text("# secret\n")
        self.server = wiz_mcp.Server(wiz_mcp.Config(workspace=self.workspace, wiz=self.wiz, idle=0, timeout=5))

    def tearDown(self) -> None:
        self.server.close()
        self.tmp.cleanup()

    def call(self, name: str, args: dict) -> dict:
        return self.server.call_tool(name, args)

    def rpc(self, method: str, params: dict) -> dict:
        responses, _ = self.server.dispatch({"jsonrpc": "2.0", "id": 1, "method": method, "params": params})
        return responses[0]

    def test_tools_are_read_only(self) -> None:
        for tool in wiz_mcp.TOOLS:
            if tool["name"] in ("search", "doc"):
                self.assertTrue(tool["annotations"]["readOnlyHint"])
                self.assertFalse(tool["annotations"]["openWorldHint"])

    def test_search_by_name_and_type(self) -> None:
        out = self.call("search", {"query": "add"})
        self.assertTrue(out["ok"], out)
        self.assertEqual(out["result"]["results"][0]["name"], "Nat.add")
        self.assertEqual(out["result"]["index"], "source")
        out = self.call("search", {"query": "(α → β) → List α → List β", "by": "type"})
        self.assertEqual(out["result"]["results"][0]["name"], "List.map")
        self.assertEqual(out["result"]["results"][0]["file"], os.path.join(self.lib, "Prelude.wiz"))
        out = self.call("search", {"query": "element", "by": "text"})
        self.assertEqual([r["name"] for r in out["result"]["results"]], ["List.map"])
        out = self.call("search", {"query": "twice"})
        self.assertEqual(out["result"]["results"][0]["module"], "Data.Extra")

    def test_search_kinds_limit_and_bad_args(self) -> None:
        out = self.call("search", {"query": "Nat", "kinds": ["constructor"]})
        self.assertEqual({r["kind"] for r in out["result"]["results"]}, {"constructor"})
        out = self.call("search", {"query": "a", "by": "text", "limit": 1})
        self.assertEqual(len(out["result"]["results"]), 1)
        self.assertGreater(out["result"]["total"], 1)
        for bad in ({"query": "x", "by": "regex"}, {"query": "x", "limit": 0}, {"query": "x", "scope": "/"},
                    {"by": "name"}, {"query": "x", "kinds": "def"}):
            self.assertEqual(self.call("search", bad)["error"]["kind"], "invalid_args", bad)

    def test_workspace_scope_skips_build_dirs(self) -> None:
        names = {r["name"] for r in self.call("search", {"query": "e", "by": "text", "scope": "workspace", "limit": 100})["result"]["results"]}
        self.assertIn("Mine.go", names)
        self.assertNotIn("Built.skip", names)
        self.assertNotIn("Nat.add", names)

    def test_symlink_out_of_the_workspace_is_not_indexed(self) -> None:
        outside = os.path.join(self.tmp.name, "Outside.wiz")
        Path(outside).write_text("def Outside.leak : Nat := 0\n")
        os.symlink(outside, os.path.join(self.workspace, "Link.wiz"))
        out = self.call("search", {"query": "leak", "scope": "workspace"})
        self.assertEqual(out["result"]["results"], [])

    def test_index_refreshes_on_change(self) -> None:
        self.assertEqual(self.call("search", {"query": "fresh", "scope": "workspace"})["result"]["total"], 0)
        Path(self.workspace, "New.wiz").write_text("def New.fresh : Nat := 0\n")
        self.assertEqual(self.call("search", {"query": "fresh", "scope": "workspace"})["result"]["total"], 1)

    def test_doc_by_name_and_module(self) -> None:
        out = self.call("doc", {"name": "Nat.add"})
        decl = out["result"]["declarations"][0]
        self.assertIn("More text.", decl["doc"])
        self.assertEqual(decl["type"], "Nat → Nat → Nat")
        self.assertTrue(out["result"]["exact"])
        out = self.call("doc", {"name": "map"})
        self.assertFalse(out["result"]["exact"])
        self.assertEqual(out["result"]["declarations"][0]["name"], "List.map")
        out = self.call("doc", {"module": "Prelude"})
        self.assertTrue(out["result"]["doc"].startswith("# Prelude"))
        self.assertIn("Nat.add", [d["name"] for d in out["result"]["declarations"]])
        self.assertEqual(self.call("doc", {"name": "nope"})["error"]["kind"], "not_found")
        self.assertEqual(self.call("doc", {"module": "Nope"})["error"]["kind"], "not_found")
        self.assertEqual(self.call("doc", {})["error"]["kind"], "invalid_args")
        self.assertEqual(self.call("doc", {"name": "a", "module": "b"})["error"]["kind"], "invalid_args")

    def test_elaborated_index_overrides_signatures(self) -> None:
        site = os.path.join(self.tmp.name, "site")
        os.makedirs(site)
        Path(site, "api.json").write_text(json.dumps([
            {"name": "Nat.double", "module": "Prelude", "kind": "def", "sig": "Nat → Nat", "doc": "Twice n."},
        ]))
        server = wiz_mcp.Server(wiz_mcp.Config(workspace=self.workspace, wiz=self.wiz, idle=0, timeout=5, doc_index=site))
        try:
            out = server.call_tool("doc", {"name": "Nat.double"})
            decl = out["result"]["declarations"][0]
            self.assertEqual(out["result"]["index"], "elaborated")
            self.assertEqual(decl["type"], "Nat → Nat")
            self.assertEqual(decl["doc"], "Twice n.")
        finally:
            server.close()

    def test_no_toolchain_library(self) -> None:
        server = wiz_mcp.Server(wiz_mcp.Config(workspace=self.workspace, wiz="/nonexistent/wiz", idle=0, timeout=5))
        try:
            self.assertEqual(server.call_tool("search", {"query": "x"})["error"]["kind"], "wiz_not_found")
            self.assertTrue(server.call_tool("search", {"query": "Mine", "scope": "workspace"})["ok"])
        finally:
            server.close()

    def test_resources(self) -> None:
        init = self.rpc("initialize", {"protocolVersion": "2025-06-18"})
        self.assertIn("resources", init["result"]["capabilities"])
        uris = [r["uri"] for r in self.rpc("resources/list", {})["result"]["resources"]]
        self.assertEqual(uris, ["wiz://trust-ledger", "wiz://trust-ledger.json", "wiz://error-codes", "wiz://stages"])
        templates = self.rpc("resources/templates/list", {})["result"]["resourceTemplates"]
        self.assertIn("wiz://error-codes/{code}", [t["uriTemplate"] for t in templates])

        def read(uri: str) -> str:
            return self.rpc("resources/read", {"uri": uri})["result"]["contents"][0]["text"]

        ledger = json.loads(read("wiz://trust-ledger.json"))
        self.assertEqual(ledger[0]["declaration"], "Classical.choice")
        self.assertEqual(len(ledger), 2)
        self.assertEqual(json.loads(read("wiz://trust-ledger/Text"))[0]["item"], "extern")
        code = json.loads(read("wiz://error-codes/unknown-identifier"))
        self.assertEqual(code["example"], "`doubel 2`")
        self.assertEqual(json.loads(read("wiz://error-codes/type-mismatch"))["example"], "`x \\| y`")
        self.assertEqual(json.loads(read("wiz://stages"))[0]["title"], "Stage 1: the kernel")
        self.assertTrue(read("wiz://stages/01-kernel").startswith("# Stage 1"))

    def test_resources_refuse_escapes_and_unknowns(self) -> None:
        for uri in ("wiz://stages/../../secret", "wiz://stages/..%2F..%2Fsecret", "wiz://stages/.hidden",
                    "wiz://error-codes/nope", "wiz://nothing", "file:///etc/passwd"):
            response = self.rpc("resources/read", {"uri": uri})
            self.assertIn("error", response, uri)
        os.symlink(os.path.join(self.tmp.name, "secret.md"), os.path.join(self.workspace, "docs", "stages", "02-leak.md"))
        self.assertIn("error", self.rpc("resources/read", {"uri": "wiz://stages/02-leak"}))
        self.assertNotIn("02-leak", [s["name"] for s in json.loads(
            self.rpc("resources/read", {"uri": "wiz://stages"})["result"]["contents"][0]["text"])])

    def test_resources_list_only_what_exists(self) -> None:
        os.remove(os.path.join(self.workspace, ".github", "trust-baseline.tsv"))
        uris = [r["uri"] for r in self.rpc("resources/list", {})["result"]["resources"]]
        self.assertEqual(uris, ["wiz://error-codes", "wiz://stages"])


if __name__ == "__main__":
    unittest.main()
