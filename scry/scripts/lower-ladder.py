"""Size ladder of parser.c-shaped inputs, cut from the real generated parser.c at
top-level and case/entry boundaries (every input is syntactically whole)."""
import sys, os, re
src, out = sys.argv[1], sys.argv[2]
L = open(src).read().split('\n')
def find(prefix, start=0):
    for i in range(start, len(L)):
        if L[i].startswith(prefix): return i
    raise SystemExit(prefix)
lex0 = find('static bool ts_lex(')
lexsw = find('  switch (state) {', lex0)
lexdef = find('    default:', lexsw)
lexend = find('}', lexdef)            # closing brace of ts_lex
header = L[:lex0]
cases = [i for i in range(lexsw + 1, lexdef) if L[i].startswith('    case ')] + [lexdef]
def lex(k):
    k = min(k, len(cases) - 1)
    return L[lex0:lexsw + 1] + L[cases[0]:cases[k]] + L[lexdef:lexend + 1]
t0 = find('static const uint16_t ts_small_parse_table[] = {')
t1 = find('};', t0)
entries = [i for i in range(t0 + 1, t1) if re.match(r'  \[\d+\] = ', L[i])] + [t1]
def table(lines):
    # the first entries covering about `lines` lines
    cut = next((e for e in entries if e - t0 - 1 >= lines), t1)
    return L[t0:cut] + ['};']
def write(name, parts):
    p = os.path.join(out, name + '.c')
    open(p, 'w').write('\n'.join(parts) + '\n')
    print(name, os.path.getsize(p))
# ladder A: the whole ts_lex, growing table after it (file size grows, lowered work fixed)
for m in (0, 6000, 12000, 25000, 52000):
    write('A-table%05d' % m, header + lex(10**9) + table(m))
# ladder B: no table, growing ts_lex (lowered work grows, file grows a little)
for k in (40, 80, 160, 324):
    write('B-lex%03d' % k, header + lex(k))
# ladder C: growing ts_lex with a fixed 25k-line table after it
for k in (40, 80, 160, 324):
    write('C-lex%03d-t25k' % k, header + lex(k) + table(25000))
