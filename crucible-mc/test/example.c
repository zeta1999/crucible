#include <svcomp.h>

void f () {
  int x = __VERIFIER_nondet_int();
  __VERIFIER_assume(x >= 0);
  int j = 5;

  while (j > 0) {
    int i = 5;
    while (i > 0) {
      __VERIFIER_assert(x >= 0 && i * i < 5);
      --i;
    }
    --j;
  }
}

