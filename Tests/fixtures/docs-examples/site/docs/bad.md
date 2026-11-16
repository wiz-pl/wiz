# Docs examples fixture: what the checker must report

[missing](missing.md)

`examples/not-there.wiz` does not exist.

```wiz
FAIL
```

```wiz run
import IO

def main : IO Unit := IO.println "actual"
```

```text
not the output
```

```wiz wat
def a_bad_marker : Nat := 1
```
