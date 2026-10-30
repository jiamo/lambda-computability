#include <stdio.h>
#include <string.h>

#include "ct/version.h"

int main(void) {
  if (strcmp(ct_version(), "0.1.0") != 0) {
    fprintf(stderr, "unexpected version %s\n", ct_version());
    return 1;
  }
  return 0;
}
