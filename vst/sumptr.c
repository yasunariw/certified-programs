#include <stddef.h>

typedef union sslval {
  int ssl_int;
  void *ssl_ptr;
} *loc;
#define READ_LOC(x,y) (*(x+y)).ssl_ptr
#define READ_INT(x,y) (*(x+y)).ssl_int
#define WRITE_LOC(x,y,z) (*(x+y)).ssl_ptr = z
#define WRITE_INT(x,y,z) (*(x+y)).ssl_int = z


void sumptr(loc x) {
  int a2 = READ_INT(x,0);
  int b2 = READ_INT(x,1);
  WRITE_INT(x,2,a2 + b2);
}
