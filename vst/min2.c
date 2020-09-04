#include <stddef.h>

typedef union sslval {
  int ssl_int;
  void *ssl_ptr;
} *loc;
#define READ_LOC(x,y) (*(x+y)).ssl_ptr
#define READ_INT(x,y) (*(x+y)).ssl_int
#define WRITE_LOC(x,y,z) (*(x+y)).ssl_ptr = z
#define WRITE_INT(x,y,z) (*(x+y)).ssl_int = z


void min2(loc r, int x, int y) {
  if((x <= y)) {
    WRITE_INT(r, 0, x);
    return;
  } else {
    WRITE_INT(r, 0, y);
    return;
  }
}
