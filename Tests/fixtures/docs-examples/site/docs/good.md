# Docs examples fixture: a clean page

```wiz
def id {0 A : Type} (1 x : A) : A := x
```

```wiz run
import IO

def main : IO Unit := IO.println "hello from fixture"
```

```
$ wiz run examples/hello.wiz
hello from fixture
```

<!-- no-check: a fragment that uses a definition from the page's prose -->
```wiz no-check
def a_fragment : Nat := the_page_defines_this_above
```

```sh
this is not a Wiz block
```

[the example](../examples/hello.wiz), [this page](good.md#docs-examples-fixture-a-clean-page),
[external](https://example.com/docs), [anchor](#docs-examples-fixture-a-clean-page).

`examples/hello.wiz` is also mentioned in prose.
