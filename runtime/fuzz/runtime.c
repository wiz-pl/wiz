/* The C runtime as one translation unit for the fuzzer builds, the same way
   scripts/test-sanitizers.sh builds it: `-DWIZ_API=` gives the object ABI, so the
   harnesses include only `wiz_rt.h`. Kept in step with the area order used by the
   sanitizer script and by generated C. */
#include "wiz_rt.h"
#include "rt_core.inc"
#include "rt_num.inc"
#include "rt_words.inc"
#include "rt_data.inc"
#include "rt_sys.inc"
#include "rt_con.inc"
