#include <stddef.h>

extern void free(void *p);

void listfree(void* x) {
  if (x == NULL) { return; }
  else {
    void* nxt2 = (void *) ((void **)x)[1];
    listfree(nxt2);
    free(x);
  }
}

