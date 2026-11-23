# Feral's residual obligations: a checked list

Status: 2026-11-22, lane `recs-linear-claims` (R7 of
`wiz-notes/sota-linear-effects.md`). This is the list of properties the Feral
**lowering** must preserve but that the kernel does not prove about the Rust source.
Each item names a negative test and says honestly where the check lives: the front
end's region checker, the shape of the generated Wiz, or `lib/Region.wiz`'s types.

The kernel proves the *lowered* program is well typed. It does not prove that lowering
preserves Rust's meaning; that is the trusted step, and these are its obligations.

| # | obligation | negative test | status |
|---|---|---|---|
| i | **Rebind the lender to `Lent`.** A mutable borrow scope replaces the lender's name with a `Lent ρ S` token, so the lender cannot be read or borrowed again while the borrow lives (E0502; E0499 for a second `&mut`). | `rejected/surface/E0502_use_while_mut` and its hand lowering `rejected/E0502_use_while_mut.wiz`, run by `Tests/Feral.lean` case *"rejected/E0502_use_while_mut: rejected by the front end and by the kernel"*; the kernel's own known gap is pinned by `Tests/Groups/Regions.lean` case *"linear handles: a scope's handle is used once and handed back on every path (formerly KNOWN GAPs 1 and 3)"*. | **front-end + lowering**, not kernel types. The lender is an ω value: a body that names the `Lent` token differently can still read it, and the `regions` test pins that acceptance as a KNOWN GAP. Closing it needs linear lenders and a `Copy` notion (K3), R4. |
| ii | **Never pack a region into a scope's result type.** A scope's `B` is chosen outside its fresh region, but `B := (0 r : Region) × Shr r A` is a closed type that would carry `ρ` and its handle out. | `drafts/feral/rejected/region_pack_shr.wiz` (shared borrow) and `region_pack_scope.wiz` (`Region.scope`), run by `Tests/Feral.lean` case *"hand-written Wiz against lib/Region.wiz: a duplicated handle and a packed region are rejected"*; the same hole is a rejection in `Tests/Groups/Regions.lean` case *"R2: a scope's result type may not quantify over its fresh region (RegionFree B)"*. | **kernel types** since R2: every scope asks for `[RegionFree B]`, there is no instance for `Region`, and no dependent Σ/Π over it. The lowering names `S`, `B` (and `H`) at every scope (`drafts/feral/LOWERING.md` L5), so the instance problem is posed at `B`; a user type gets an instance from its declaration (Feral emits one per `struct`/`enum`). An `instance : RegionFree T` is a trust declaration, like an axiom. |
| iii | **Emit each handle at most once.** A `&mut` handle is used exactly once and handed back on every path, including error paths (D8). | `drafts/feral/rejected/dup_handle.wiz` (duplicates a `Uniq`), run by the same `Tests/Feral.lean` case; the Feral-level `E0499_two_mut` and `Tests/Groups/Regions.lean` case *"linear handles: a scope's handle is used once and handed back on every path (formerly KNOWN GAPs 1 and 3)"* (`swap r r`, a handle kept past its scope). | **kernel types**: quantity 1 with `Result1`/`Borrowed` on both branches. The lowering's part is that every Wiz scope it emits has this shape; a bad lowering fails the quantity check. |
| iv | **Discharge `RegionFree B` once per scope.** Every lowered scope names its result type `B` and relies on instance resolution; the lowering must not add an instance for a type that packs a region. | the two `region_pack_*` fixtures above (rejected by the missing instance), plus every `surface/NN` program (the positive side: the instances resolve and the generated source checks). The Feral lowering emits one structural instance per user `struct`/`enum` (its types have no region parameters to quantify over); `drafts/feral/lib/FeralCore.wiz` declares the ones for `U64`, `Vec` and `Flow`. | **kernel types** (the instance is an instance-implicit argument; an unresolvable one is a compile error). A hand-written `instance : RegionFree T := RegionFree.mk ()` for a region-packing `T` would defeat it: that is an explicit trust declaration, not a silent success. |

## Related `L21` errors already covered

| error | negative test | status |
|---|---|---|
| E0515 (return a borrow of a local) | `rejected/surface/E0515_return_local`, `E0515_return_mut` | tested, both verdicts |
| E0597 (a borrow outlives its scope; a short reference stored into a long slot) | `rejected/surface/E0597_not_long_enough`, `E0597_store_short` | tested, both verdicts |
| E0499 (two `&mut` of one local; one `&mut` used twice) | `rejected/surface/E0499_two_mut`, `inline_spec_borrow`; `Tests/Groups/Regions.lean` `dup` | tested |
| missing `'a : 'b`, the bound pointing the wrong way, a lengthened borrow | `rejected/surface/lifetime_bound_missing`, `lifetime_bound_missing_mut`, `outlives_wrong_way`; `rejected/lengthen_borrow.wiz` | tested |
| E0506 (assignment to a `Lent` lender) | `Tests/Feral.lean` case *"the lender is unusable while a named borrow of it lives (E0499, E0502, E0506)"* (`v := Vec.new` while `&mut v` lives) | tested by the front end; there is no separate `rejected/surface` fixture for E0506. |

The positive control for (ii)/(iv) is not only the existing `surface/` programs: the
`regions` case *"R2: a scope's result type may not quantify over its fresh region"*
checks an ordinary data result and a user type with its instance, and the case *"R5:
linearity is not uniqueness: a &mut scope's allocation cost is measured"* keeps the
measured allocation counts from drifting.
