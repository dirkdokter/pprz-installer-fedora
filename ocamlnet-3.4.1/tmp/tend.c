#include "caml/mlvalues.h"
value check(value d) {
  union {
    int i;
    char s[4];
  } u;
  u.i = 0x0001010101;
  return (u.s[0] == 0 ? Val_true : Val_false);
}
