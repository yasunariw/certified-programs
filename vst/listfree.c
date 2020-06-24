#include <stddef.h>

extern void free(void *p);

void listfree(int ** x) {
  if (x == NULL) { return; }
  else {
    int ** nxt2 = (int **) x[1];
    listfree(nxt2);
    free(x);
  }
}

