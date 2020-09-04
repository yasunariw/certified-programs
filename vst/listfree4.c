#include <stddef.h>

extern void free(void *p);

void listfree(void * x) {
  if((x == 0)) {
    return;
  } else {
    void * n = *((void **)x + 1);
    listfree(n);
    free(x);
    return;
  }
}
