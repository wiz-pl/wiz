# `Str` aliasing negatives

`runtime/rt_data.inc`'s `wiz_str_append`/`wiz_str_push` grow the receiver in place only
when `WIZ_RC(a) == 1` and (for append) `a != b`. These programs pin the cases that must
keep the old copying behaviour: the observable original is never mutated, whatever the
runtime does to the unique path. Each `.wiz` is compiled by the `=std` group and its
stdout is compared with the sibling `.expected` (see `Tests/Groups/Std.lean`).

| fixture | case | expected |
|---|---|---|
| `self-append.wiz` | `Str.append s s` (`a == b`) | `abcabc`, then the original `abc` |
| `shared-receiver.wiz` | receiver aliased in a pair (`rc > 1`) | original `abc`, result `abcx` |
| `shared-push.wiz` | `Str.push` receiver aliased in a pair | original `abc`, result `abcD` |
| `shared-join.wiz` | `Str.join` piece aliased in a pair | original `a`, result `ab` |

The invariant: a `Str` is immutable to its source-level owner. The fast path is sound
only because the language call consumes its operands, so `rc == 1` means no other live
value can observe the buffer; self-append is excluded separately because a realloc
would invalidate the second `memcpy` from the same object. A shared value has `rc > 1`
and is copied, so every `p.1` above is unchanged.
