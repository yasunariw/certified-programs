#include <stddef.h>

typedef union sslval {
  int ssl_int;
  void *ssl_ptr;
} *loc;
#define READ_LOC(x,y) (*(x+y)).ssl_ptr
#define READ_INT(x,y) (*(x+y)).ssl_int

extern void free(void *p);

void listfree(loc x) {
  if((x == 0)) {
    return;
  } else {
    loc n = READ_LOC(x,1);
    listfree(n);
    free(x);
    return;
  }
}

