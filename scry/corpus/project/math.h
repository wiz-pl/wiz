#ifndef PROJECT_MATH_H
#define PROJECT_MATH_H

/* FACTOR is supplied per translation unit: -DFACTOR=2 for math.c, 3 for main.c.
   The shared header is the same file in both units; only the expansion differs. */
#define SCALE(x) ((x) * FACTOR)

int add(int a, int b);
int scaled(int x);
int use_helper(int x);

#endif
