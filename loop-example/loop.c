/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
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

unsigned int global_x;

__attribute__((noinline, noclone)) int
create_one (unsigned int identifier) {
  global_x ++;
  return 1;
}

__attribute__((noinline, noclone)) int
check_one (int result) {
  global_x ++;
  return 1;
}

unsigned int
create_loop (unsigned int start, unsigned int end) {
  int f;
  int r;

  for (f = start; f < end; f += 1024) {
    r = create_one (f);
    if (! check_one (r)) {
      return 21;
    }
  }

  return end;
}


