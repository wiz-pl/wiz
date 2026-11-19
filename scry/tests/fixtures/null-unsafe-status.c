/* The CVE-2017-7659 control shape, with the pointer as a call result rather than an
   out-parameter (an out-parameter is a stack slot, which this pass does not track).
   `request_create` is external, so its result may be NULL; `request_status` always
   returns the failure code 1. The vulnerable code ignores the status. */
struct request {
  const char *method;
};

struct request *request_create(void);

static int request_status(void) {
  return 1;
}

int main(void) {
  struct request *req = request_create();
  int status = request_status();
  return req->method != 0;
}
