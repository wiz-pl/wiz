# 1 "../scry/corpus/project/math.c"
# 1 "<built-in>" 1
# 1 "<built-in>" 3
# 410 "<built-in>" 3
# 1 "<command line>" 1
# 1 "<built-in>" 2
# 1 "../scry/corpus/project/math.c" 2
# 1 "../scry/corpus/project/math.h" 1







int add(int a, int b);
int scaled(int x);
int use_helper(int x);
# 2 "../scry/corpus/project/math.c" 2

int add(int a, int b) {
  return a + b;
}

int scaled(int x) {
  return ((x) * 2);
}

static int helper(int x) {
  return x + 1;
}

int use_helper(int x) {
  return helper(x);
}
