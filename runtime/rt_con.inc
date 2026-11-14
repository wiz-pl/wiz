
/* ---- threads (stage 25a): spawning, channels, MVars, locks ----

   Ownership rule. An object with rc > 0 belongs to one thread: its count is changed with
   plain arithmetic. Before a value crosses to another thread (a forked thread's closure,
   a message, an MVar's contents) the runtime marks everything reachable from it as
   shared (`wiz_mark_mt`: rc becomes -rc), and shared counts change atomically. rc == 0
   is immortal (hoisted constants), never counted. So a shared object only points to
   shared or immortal objects; in-place updates need rc == 1, which a shared object
   never has, and a shared thunk is forced under a lock and its value marked shared. */

static void wiz_mark_mt(wiz_val v) {
  size_t cap = 64, n = 0;
  wiz_val *st = (wiz_val *)malloc(cap * sizeof(wiz_val));
  st[n++] = v;
#define WIZ_PUSH(x) do { wiz_val y_ = (x); if (!WIZ_IS_SCALAR(y_) && WIZ_RC((wiz_hdr *)y_) > 0) { \
    if (n == cap) { cap *= 2; st = (wiz_val *)realloc(st, cap * sizeof(wiz_val)); } st[n++] = y_; } } while (0)
  while (n) {
    wiz_val x = st[--n];
    if (WIZ_IS_SCALAR(x)) continue;
    wiz_hdr *h = (wiz_hdr *)x;
    if (h->rc <= 0) continue; /* already shared, or immortal */
    h->rc = -h->rc;
    switch (h->tag) {
    case WIZ_TAG_CLO: for (uint32_t i = 0; i < h->size; i++) WIZ_PUSH(((wiz_clo *)x)->args[i]); break;
    case WIZ_TAG_THUNK: { wiz_thunk *t = (wiz_thunk *)x; WIZ_PUSH(t->fn ? t->fn : t->val); break; }
    case WIZ_TAG_ARRAY: { wiz_array *a = (wiz_array *)x; for (size_t i = 0; i < a->len; i++) WIZ_PUSH(a->data[i]); break; }
    case WIZ_TAG_MAP: { wiz_map *m = (wiz_map *)x;
      for (size_t i = 0; i < m->cap; i++)
        if (m->keys[i]) { WIZ_PUSH(m->keys[i]); WIZ_PUSH(m->vals[i]); }
      break; }
    case WIZ_TAG_WMAP: { wiz_wmap *m = (wiz_wmap *)x;
      for (size_t i = 0; i < m->cap; i++) if (m->vals[i]) WIZ_PUSH(m->vals[i]);
      break; }
    case WIZ_TAG_ITAB: { wiz_itab *t = (wiz_itab *)x; for (size_t i = 0; i < t->count; i++) WIZ_PUSH(t->strs[i]); break; }
    case WIZ_TAG_BIG: case WIZ_TAG_RAW: case WIZ_TAG_EXT: case WIZ_TAG_BYTES: case WIZ_TAG_STR: case WIZ_TAG_WARRAY: break;
    default: for (uint32_t i = 0; i < h->size; i++) WIZ_PUSH(((wiz_ctor *)x)->fields[i]);
    }
  }
#undef WIZ_PUSH
  free(st);
}

/* every thread but main is counted, so the program can wait for them before it checks
   for leaks; a finished thread adds its allocation balance to wiz_live_exited */
static pthread_mutex_t wiz_threads_mu = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t wiz_threads_cv = PTHREAD_COND_INITIALIZER;
static int64_t wiz_threads_running = 0;
static int64_t wiz_live_exited = 0;

typedef struct { wiz_val fn; wiz_val arg; } wiz_spawn_args;

static void *wiz_thread_main(void *p) {
  wiz_spawn_args a = *(wiz_spawn_args *)p;
  free(p);
  /* `fn : (1 c : Chan …) → IO Unit`: apply it to its argument and a world */
  wiz_val args[2] = {a.arg, WIZ_BOX(0)};
  wiz_val r = wiz_apply(a.fn, 2, args);
  wiz_dec(r);
  pthread_mutex_lock(&wiz_threads_mu);
  wiz_live_exited += wiz_live;
  wiz_threads_running--;
  pthread_cond_broadcast(&wiz_threads_cv);
  pthread_mutex_unlock(&wiz_threads_mu);
  return NULL;
}

/* run `fn arg world` on a new thread; `fn` must be shared already, `arg` is moved */
static void wiz_spawn(wiz_val fn, wiz_val arg) {
  wiz_spawn_args *a = (wiz_spawn_args *)malloc(sizeof *a);
  a->fn = fn; a->arg = arg;
  const char *mb = getenv("WIZ_THREAD_STACK_MB");
  size_t size = (size_t)(mb ? atol(mb) : 256) << 20;
  pthread_attr_t attr;
  pthread_attr_init(&attr);
  pthread_attr_setstacksize(&attr, size);
  pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED);
  pthread_mutex_lock(&wiz_threads_mu);
  wiz_threads_running++;
  pthread_mutex_unlock(&wiz_threads_mu);
  pthread_t t;
  if (pthread_create(&t, &attr, wiz_thread_main, a) != 0) wiz_panic("can't start a thread");
  pthread_attr_destroy(&attr);
}

static void wiz_wait_threads(void) {
  pthread_mutex_lock(&wiz_threads_mu);
  while (wiz_threads_running > 0) pthread_cond_wait(&wiz_threads_cv, &wiz_threads_mu);
  pthread_mutex_unlock(&wiz_threads_mu);
}

/* a Σ pair ⟨a, b⟩ */
static wiz_val wiz_pair(wiz_val a, wiz_val b) {
  wiz_val p = wiz_ctor_new(0, 2);
  WIZ_SET(p, 0, a); WIZ_SET(p, 1, b);
  return p;
}

/* -- channels (lib/Session.wiz): two endpoints, one queue of messages towards each.
   Sending never blocks; receiving waits for a message. Each endpoint is a foreign
   object; the channel goes when both are closed. -- */

typedef struct wiz_msg { wiz_val v; struct wiz_msg *next; } wiz_msg;
typedef struct wiz_chan wiz_chan;
typedef struct { wiz_chan *ch; int side; } wiz_end;
struct wiz_chan {
  pthread_mutex_t mu;
  pthread_cond_t cv;
  wiz_msg *head[2], *tail[2]; /* messages to side 0, to side 1 */
  int ends;
  wiz_end end[2];
};

static void wiz_chan_end_fin(void *p) {
  wiz_end *e = (wiz_end *)p;
  wiz_chan *ch = e->ch;
  pthread_mutex_lock(&ch->mu);
  int last = --ch->ends == 0;
  pthread_mutex_unlock(&ch->mu);
  if (!last) return;
  for (int s = 0; s < 2; s++)
    for (wiz_msg *m = ch->head[s]; m;) { wiz_msg *nx = m->next; wiz_dec(m->v); free(m); m = nx; }
  pthread_mutex_destroy(&ch->mu);
  pthread_cond_destroy(&ch->cv);
  free(ch);
}

static wiz_chan *wiz_chan_of(wiz_val c, int *side) {
  wiz_end *e = (wiz_end *)((wiz_ext *)c)->ptr;
  *side = e->side;
  return e->ch;
}

/* `Chan.forkRaw child`: a new channel; `child` runs on end 1 in a new thread, the
   caller gets end 0 */
WIZ_API wiz_val wiz_chan_fork(wiz_val child) {
  wiz_chan *ch = (wiz_chan *)calloc(1, sizeof(wiz_chan));
  pthread_mutex_init(&ch->mu, NULL);
  pthread_cond_init(&ch->cv, NULL);
  ch->ends = 2;
  for (int s = 0; s < 2; s++) { ch->end[s].ch = ch; ch->end[s].side = s; }
  wiz_val e0 = wiz_out_ptr(&ch->end[0], wiz_chan_end_fin);
  wiz_val e1 = wiz_out_ptr(&ch->end[1], wiz_chan_end_fin);
  wiz_mark_mt(child);
  wiz_spawn(child, e1);
  return e0;
}

/* `Chan.sendRaw c a`: queue `a` for the other end; the endpoint comes back */
WIZ_API wiz_val wiz_chan_send(wiz_val c, wiz_val a) {
  int side;
  wiz_chan *ch = wiz_chan_of(c, &side);
  wiz_mark_mt(a);
  wiz_msg *m = (wiz_msg *)malloc(sizeof *m);
  m->v = a; m->next = NULL;
  int to = 1 - side;
  pthread_mutex_lock(&ch->mu);
  if (ch->tail[to]) ch->tail[to]->next = m; else ch->head[to] = m;
  ch->tail[to] = m;
  pthread_cond_broadcast(&ch->cv);
  pthread_mutex_unlock(&ch->mu);
  return c;
}

/* `Chan.recvRaw c`: wait for a message; ⟨message, endpoint⟩ */
WIZ_API wiz_val wiz_chan_recv(wiz_val c) {
  int side;
  wiz_chan *ch = wiz_chan_of(c, &side);
  pthread_mutex_lock(&ch->mu);
  while (!ch->head[side]) pthread_cond_wait(&ch->cv, &ch->mu);
  wiz_msg *m = ch->head[side];
  ch->head[side] = m->next;
  if (!m->next) ch->tail[side] = NULL;
  pthread_mutex_unlock(&ch->mu);
  wiz_val v = m->v;
  free(m);
  return wiz_pair(v, c);
}

WIZ_API void wiz_chan_close(wiz_val c) { wiz_dec(c); }

/* -- MVars and locks (lib/MVar.wiz) -- */

typedef struct {
  pthread_mutex_t mu;
  pthread_cond_t cv;
  int full;
  wiz_val v;
} wiz_mvar;

static void wiz_mvar_fin(void *p) {
  wiz_mvar *m = (wiz_mvar *)p;
  if (m->full) wiz_dec(m->v);
  pthread_mutex_destroy(&m->mu);
  pthread_cond_destroy(&m->cv);
  free(m);
}

WIZ_API wiz_val wiz_mvar_new(void) {
  wiz_mvar *m = (wiz_mvar *)calloc(1, sizeof(wiz_mvar));
  pthread_mutex_init(&m->mu, NULL);
  pthread_cond_init(&m->cv, NULL);
  m->v = WIZ_BOX(0);
  return wiz_out_ptr(m, wiz_mvar_fin);
}

static wiz_val wiz_mvar_take_(wiz_val mv, int keep) {
  wiz_mvar *m = (wiz_mvar *)((wiz_ext *)mv)->ptr;
  pthread_mutex_lock(&m->mu);
  while (!m->full) pthread_cond_wait(&m->cv, &m->mu);
  wiz_val v = m->v;
  if (keep) wiz_inc(v);
  else { m->full = 0; m->v = WIZ_BOX(0); pthread_cond_broadcast(&m->cv); }
  pthread_mutex_unlock(&m->mu);
  wiz_dec(mv);
  return v;
}

WIZ_API void wiz_mvar_put(wiz_val mv, wiz_val a) {
  wiz_mvar *m = (wiz_mvar *)((wiz_ext *)mv)->ptr;
  wiz_mark_mt(a);
  pthread_mutex_lock(&m->mu);
  while (m->full) pthread_cond_wait(&m->cv, &m->mu);
  m->v = a; m->full = 1;
  pthread_cond_broadcast(&m->cv);
  pthread_mutex_unlock(&m->mu);
  wiz_dec(mv);
}

WIZ_API wiz_val wiz_mvar_new_full(wiz_val a) {
  wiz_val mv = wiz_mvar_new();
  wiz_inc(mv);
  wiz_mvar_put(mv, a);
  return mv;
}
WIZ_API wiz_val wiz_mvar_take(wiz_val mv) { return wiz_mvar_take_(mv, 0); }
WIZ_API wiz_val wiz_mvar_read(wiz_val mv) { return wiz_mvar_take_(mv, 1); }
/* the hole is a token with nothing in it */
WIZ_API wiz_val wiz_mvar_take_hole(wiz_val mv) { return wiz_pair(wiz_mvar_take_(mv, 0), WIZ_BOX(0)); }
WIZ_API void wiz_mvar_fill(wiz_val mv, wiz_val hole, wiz_val a) { wiz_dec(hole); wiz_mvar_put(mv, a); }

/* lib/Handle.wiz: the obligation to release a handle is an empty box (as an MVar hole) */
WIZ_API wiz_val wiz_handle_own(void) { return WIZ_BOX(0); }
WIZ_API void wiz_handle_disown(wiz_val tok) { wiz_dec(tok); }
/* lib/Ref.wiz: a cell is an MVar that stays full; its ownership token is a box with
   nothing in it (as an MVar hole). The token's index (the cell's value) is a ghost: the
   types in Ref.wiz are trusted to keep it equal to what the cell holds. */
WIZ_API wiz_val wiz_ref_new(wiz_val a) { return wiz_pair(wiz_mvar_new_full(a), WIZ_BOX(0)); }
WIZ_API wiz_val wiz_ref_read(wiz_val mv, wiz_val tok) { return wiz_pair(wiz_mvar_take_(mv, 1), wiz_pair(WIZ_BOX(0), tok)); }
WIZ_API wiz_val wiz_ref_write(wiz_val mv, wiz_val a, wiz_val tok) {
  wiz_inc(mv); /* take_ and put each consume one reference */
  wiz_dec(wiz_mvar_take_(mv, 0));
  wiz_mvar_put(mv, a);
  return tok;
}
/* the value goes now (take_ empties the cell and consumes our reference to it); the cell
   itself when the last Loc does */
WIZ_API void wiz_ref_free(wiz_val mv, wiz_val tok) { wiz_dec(tok); wiz_dec(wiz_mvar_take_(mv, 0)); }

/* a lock is a binary semaphore, so a guard may be released by another thread */
typedef struct {
  pthread_mutex_t mu;
  pthread_cond_t cv;
  int held;
} wiz_lock;

static void wiz_lock_fin(void *p) {
  wiz_lock *l = (wiz_lock *)p;
  pthread_mutex_destroy(&l->mu);
  pthread_cond_destroy(&l->cv);
  free(l);
}
WIZ_API wiz_val wiz_lock_new(void) {
  wiz_lock *l = (wiz_lock *)calloc(1, sizeof(wiz_lock));
  pthread_mutex_init(&l->mu, NULL);
  pthread_cond_init(&l->cv, NULL);
  return wiz_out_ptr(l, wiz_lock_fin);
}
WIZ_API wiz_val wiz_lock_acquire(wiz_val lv) {
  wiz_lock *l = (wiz_lock *)((wiz_ext *)lv)->ptr;
  pthread_mutex_lock(&l->mu);
  while (l->held) pthread_cond_wait(&l->cv, &l->mu);
  l->held = 1;
  pthread_mutex_unlock(&l->mu);
  wiz_dec(lv);
  return WIZ_BOX(0);
}
WIZ_API void wiz_lock_release(wiz_val lv, wiz_val g) {
  wiz_lock *l = (wiz_lock *)((wiz_ext *)lv)->ptr;
  wiz_dec(g);
  pthread_mutex_lock(&l->mu);
  l->held = 0;
  pthread_cond_broadcast(&l->cv);
  pthread_mutex_unlock(&l->mu);
  wiz_dec(lv);
}

/* the objects still alive, once every thread has finished */
static int64_t wiz_live_total(void) {
  wiz_wait_threads();
  return wiz_live + wiz_live_exited;
}

/* run `main : IO A`: apply it to the world, and drop the result */
WIZ_API int wiz_finish_io(wiz_val main) {
  wiz_val w = WIZ_BOX(0);
  wiz_val r = wiz_apply(main, 1, &w);
  wiz_dec(r);
  int64_t live = wiz_live_total();
  if (live != 0) { fprintf(stderr, "wiz: %ld objects leaked\n", (long)live); wiz_report_leaks(); return 2; }
  return 0;
}

WIZ_API int wiz_finish(wiz_val r) {
  wiz_print(r);
  putchar('\n');
  wiz_dec(r);
  int64_t live = wiz_live_total();
  if (live != 0) { fprintf(stderr, "wiz: %ld objects leaked\n", (long)live); wiz_report_leaks(); return 2; }
  return 0;
}

/* ---- main: run on a thread with a big stack (deep recursion is normal in functional
   code); $WIZ_STACK_MB sets its size, default 1024 ---- */

typedef struct { wiz_val (*entry)(void); int io; int rc; } wiz_main_args;

static void *wiz_main_thread(void *p) {
  wiz_main_args *a = (wiz_main_args *)p;
  wiz_val v = a->entry();
  a->rc = a->io ? wiz_finish_io(v) : wiz_finish(v);
  return NULL;
}

WIZ_API int wiz_run_main(wiz_val (*entry)(void), int io) {
  wiz_main_args args = {entry, io, 0};
  wiz_track_init();
  const char *mb = getenv("WIZ_STACK_MB");
  size_t size = (size_t)(mb ? atol(mb) : 1024) << 20;
  pthread_attr_t attr;
  pthread_attr_init(&attr);
  pthread_attr_setstacksize(&attr, size);
  pthread_t t;
  if (pthread_create(&t, &attr, wiz_main_thread, &args) != 0) return wiz_main_thread(&args), args.rc;
  pthread_join(t, NULL);
  return args.rc;
}
