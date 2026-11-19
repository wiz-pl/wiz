/* The fixed control: `request_status` always returns 1, so `status == 0` is
   constant-false and the NULL dereference is unreachable. */
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
  if (status == 0) {
    return req->method != 0;
  }
  return 1;
}
