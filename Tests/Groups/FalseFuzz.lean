import Tests.FalseFuzz

/-!
# The `False` fuzzer's test group

`Tests/FalseFuzz.lean` holds the campaign (and `tests --false-fuzz …`); the bounded
campaign is registered as an ordinary test case here, so the registry is the directory
(`Tests/Groups/`) and `.github/test-shards.json` runs `=false-fuzz` in the kernel shard.
-/

namespace Tests.FalseFuzz

builtin_initialize registerGroup group

end Tests.FalseFuzz
