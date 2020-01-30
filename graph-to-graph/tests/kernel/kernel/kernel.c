/*
 * Copyright 2015, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
*/

/*
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
*/

void halt(void)
{
    while (1) ;
}

int g (int i) {
//  return i * 8 + (i & 15);
  return i  + 1;
}

long long m(long long i) {
  return i - 1;
}

void f(void) {
    volatile int b = 0;
    b++;
}

long loop(long v) {
    for (int i = 0; i < 10 + v; i++) {
        v += i;
    }

    for (int j = 0; j < 20 + v; j++) {
      v *= (j + v);
    }
    return v;
}

long zero(void)
{
  return 16;
}


long call_zero(void)
{
  volatile long long a = zero();

  return m(a);
}
int main(void)
{
    volatile int a = 0;
    f();

//    for (int i = 0; i < 10; i++)
 //   {
    //int c = g(10);
    //int d = g(20);
        //a = g(i);
        //asm volatile ("addi %0, %0, 1":"+r"(a));
        a++;
        //a++;

  //  }
      a = zero();
      a = loop(20);
      return 2;
}
