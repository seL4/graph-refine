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

void plus(void)
{
  long a = 100;
  long b = 200;
  long c = a + b * a;
}

void halt(void)
{
    while (1) ;
}

int g (int i) {
//  return i * 8 + (i & 15);
  return i  + 1;
}

long m(long i) {
  return i - 1;
}

unsigned long f(void) {
    unsigned long int b = 0;
    b++;
    return b;
}

long loop(long v) {
    for (int i = 0; i < 10; i++) {
        v += i;
    }
/*
    for (int j = 0; j < 20; j++) {
      v *= (j + v);
    }
    */
    return v;
}

unsigned long zero(void)
{
  unsigned long a = 100;
  return (unsigned long)16 + a;
}

unsigned long vzero(void)
{
  volatile unsigned long a = 100;
  return (unsigned long)16 + a;
}

long call_zero(void)
{
  long long a = zero();

  return m(a);
}

long main(void)
{
    long a = 0;
    //f();

//    for (int i = 0; i < 10; i++)
 //   {
    //int c = g(10);
    //int d = g(20);
        //a = g(i);
        //asm volatile ("addi %0, %0, 1":"+r"(a));
        a++;
        //a++;

  //  }
      //a = zero();
      a = loop(20);
      return a;
}
