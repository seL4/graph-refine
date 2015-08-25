/*
 * Copyright 2015, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
*/

int
g (int i) {
  return i * 8 + (i & 15);
}

void
f (int *p, int x) {
  int i;

  for (i = x; i < 100; i ++) {
    p[i] = g (i);
  }
}


