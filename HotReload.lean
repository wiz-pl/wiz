import HotReload.Basic
import HotReload.Check
import HotReload.Interp
import HotReload.Tests

/-!
# Hot-reload P0

The model behind `/workspace/wiz-notes/hot-reload.md` §12. It is a separate,
non-default library: `lake build` alone does not build it, and nothing under
`Wiz/`, `lib/` or `Main.lean` imports it. See `HotReload/README.md` for the
roadblocks (what needs a build or a measurement) and `HotReload/Tests.lean` for
the acceptance cases, which are written but **not run** in this lane.

The short version of the model:

* `Observable` is a slot id; `Pinned` is a generation id; `read` is a table load;
* a generation is immutable and a swap appends one (`Runtime.commit`);
* a slot has a stable surface name and a per-body internal name `x@<body rev>`;
* the memo revision mixes the body rev with the callees' revisions, and is
  recomputed to a fixed point (generation-keyed on a cycle);
* the cache stores the generation-independent kernel verdict, keyed by type, body,
  mentioned helpers, witness and kernel version.
-/
