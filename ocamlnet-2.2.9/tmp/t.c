#include <stdlib.h>
#include <stdio.h>
#include "tcl.h"

do_something () {
    void (*x)(int);
    x = Tcl_Exit;
    exit(0);
}
