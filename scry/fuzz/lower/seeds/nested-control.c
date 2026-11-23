/* Nested blocks and while loops: CFG/fixpoint shape. */
int f(void) {
  while (1) {
    while (1) {
      if (1) { return 0; }
    }
  }
}
