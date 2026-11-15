# `grail-index`: a static package index

This directory is a complete, small **index repository** in the layout `grail update`
reads. It is also the template for the intended `wiz-pl/grail-index`: replace the three
example packages with real releases, keep the layout and the generator.

```
index.wiz                 the index's own manifest: name, format, packages (Wiz code)
registry.sexpr            index metadata clients may read (name, format, updated)
index/NAME.sexpr          the static index, one file per package
entries/NAME.sexpr.in     the templates make.sh renders index/NAME.sexpr from
sources/NAME-VERSION/     unpacked sources; the input to the generator
packages/NAME-VERSION.tar.gz   deterministic release archives (checked in)
make.sh                   generation: archives, hashes, index/*.sexpr, index.sexpr
index/snapshot.sexpr      optional signed state (+ .sig), not generated here
index.sexpr               every package in one document (a file index)
```

## Generation rules

1. **The sources are the truth.** `sources/NAME-VERSION/` is the package at that release
   (its `grail.wiz` and `lib` roots). The archive is made from it, never edited after.
2. **The archive is deterministic.** `make.sh` runs
   `tar --sort=name --mtime=@0 --owner=0 --group=0 --numeric-owner … | gzip -n`, so the
   bytes depend on the sources only. A real index built from git tags uses
   `scripts/grail-archive.sh` instead (`git archive --prefix=NAME-VERSION/ | gzip -n`);
   both make the SHA-256 re-derivable by anyone.
3. **The entry is generated, then reviewed.** `make.sh` copies `entries/NAME.sexpr.in`
   to `index/NAME.sexpr` and fills each `@SHA:NAME-VERSION@` with the archive's hash.
   Publish a new release by adding `sources/NAME-VERSION/` and a template entry, then
   running `./make.sh`. `grail publish ARCHIVE --source URL` prints the `(version …)`
   node from a package's manifest and archive, including its `(modules …)`.
4. **`index.wiz` lists exactly the packages on disk.** It is Wiz code, evaluated by
   `grail index check`; adding a package means adding `Index.package "NAME"` and the
   `index/NAME.sexpr` it generates. `registry.sexpr` repeats the name and format so a
   plain-text client can read them without Wiz.
5. **`name@version` is immutable.** Never edit a published `(version …)` or its archive;
   publish a new version. A bad release is `(yanked VERSION "why")`, which stops new
   resolutions while old locks keep working.
6. **`source` is relative in this example** (`packages/NAME-VERSION.tar.gz`), so the
   checkout is self-contained. A hosted index uses absolute release URLs; both are
   accepted, and a relative source resolves against the index root.

## Using it

```sh
# resolve a package against this checkout
grail update --index examples/grail-index

# the single-file form (one document holding every package)
grail update --index examples/grail-index/index.sexpr

# validate: entries, requirements, local archive hashes, module-prefix conflicts,
# and index.wiz against the files on disk. No network.
scripts/grail-index-check.sh examples/grail-index
```

The same directory is used by the `=grail-index` tests. A hosted copy is a git URL:
`grail update --index https://github.com/wiz-pl/grail-index` (or a `file://` URL in a
test), and `grail index check URL --fetch` validates it after cloning.

## Signing and hosting

This layout is deliberately static: a git repository of text files plus immutable
tarballs. The archive SHA-256 in the index chains the bytes; the index's git history is
the audit log. An index can also publish `index/snapshot.sexpr` and sign it with
`ssh-keygen -Y sign -n grail-index`; `grail update --require-signature --allowed-signers
FILE` verifies it offline and pins the key, sequence and digest in `grail.lock`. This
example is **unsigned** (there is no key to commit): see
[docs/stages/23-grail/index-repository.md](../../docs/stages/23-grail/index-repository.md)
for the format, the TUF/Sigsum staging and the remaining gaps (freshness, rotation, a
transparency log). Do not describe a hash as authorship.
