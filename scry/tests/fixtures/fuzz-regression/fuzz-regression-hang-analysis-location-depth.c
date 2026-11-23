/* F54: the points-to key used to be `(fnv(name) XOR var) * c + d`. The FNV hashes of
   `unit1`/`unit2`/`unit3` differ by one in the low bit, so `(unit1, v)` and
   `(unit2, v - 1)` were the same map key. The merged registers fed `anyOff`/`field`
   back into themselves and the location set grew one level per fixpoint round. The
   `if` chain raises the round fuel enough that the old analysis ran for tens of
   seconds on this file (and the original 4-file fuzzer project for minutes); the
   strong key and the finite location bound make it finish. Every function has the
   pointer parameter at index 2, which is what the colliding keys need. */

int unit1(int x, int y, char *p) {
  int v1 = (char0++);
  if (x > 3) { y = y + v1; }
  p[0] = x[NULL];
}

int unit2(int x, int y, char *p) {
  if (x > 1) { y = y + v3; }
  while (y > 0) { y = y - 1; }
}

int unit3(int x, int y, char *p) {
  if (x > 0) { y = y + 0; }
  if (x > 1) { y = y + 1; }
  if (x > 2) { y = y + 2; }
  if (x > 3) { y = y + 3; }
  if (x > 4) { y = y + 4; }
  if (x > 5) { y = y + 5; }
  if (x > 6) { y = y + 6; }
  if (x > 7) { y = y + 7; }
  if (x > 8) { y = y + 8; }
  if (x > 9) { y = y + 9; }
  if (x > 10) { y = y + 10; }
  if (x > 11) { y = y + 11; }
  if (x > 12) { y = y + 12; }
  if (x > 13) { y = y + 13; }
  if (x > 14) { y = y + 14; }
  if (x > 15) { y = y + 15; }
  if (x > 16) { y = y + 16; }
  if (x > 17) { y = y + 17; }
  if (x > 18) { y = y + 18; }
  if (x > 19) { y = y + 19; }
  if (x > 20) { y = y + 20; }
  if (x > 21) { y = y + 21; }
  if (x > 22) { y = y + 22; }
  if (x > 23) { y = y + 23; }
  if (x > 24) { y = y + 24; }
  if (x > 25) { y = y + 25; }
  if (x > 26) { y = y + 26; }
  if (x > 27) { y = y + 27; }
  if (x > 28) { y = y + 28; }
  if (x > 29) { y = y + 29; }
}
