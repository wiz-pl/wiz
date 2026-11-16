# usage: resolve.py FILE SPEC...   SPEC per hunk in order: "o" ours, "t" theirs, "ot" ours then theirs,
# "to", or "f:PATH" (replace the hunk with the contents of PATH)
import sys, re
p = sys.argv[1]; specs = sys.argv[2:]
lines = open(p).read().split('\n')
out = []; i = 0; h = 0
while i < len(lines):
    l = lines[i]
    if l.startswith('<<<<<<< '):
        ours = []; theirs = []; i += 1
        while not lines[i].startswith('======='): ours.append(lines[i]); i += 1
        i += 1
        while not lines[i].startswith('>>>>>>> '): theirs.append(lines[i]); i += 1
        i += 1
        sp = specs[h]; h += 1
        if sp.startswith('f:'): out += open(sp[2:]).read().rstrip('\n').split('\n')
        else:
            for c in sp: out += ours if c == 'o' else theirs
        continue
    out.append(l); i += 1
assert h == len(specs), (h, len(specs))
open(p, 'w').write('\n'.join(out))
print(p, h, 'hunks')
