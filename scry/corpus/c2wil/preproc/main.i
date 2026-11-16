# 0 "corpus/c2wil/preproc/main.c"
# 0 "<built-in>"
# 0 "<command-line>"
# 1 "corpus/c2wil/preproc/main.c"
# 1 "corpus/c2wil/preproc/inc.h" 1



static int bump(int x) {
  return x + 1;
}
# 2 "corpus/c2wil/preproc/main.c" 2



int main(void) {
  int a = ((3) * 2);

  int b = a + 5;



  return bump(b);
}
