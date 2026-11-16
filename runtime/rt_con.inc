
/* ---- threads (stage 25a): spawning, channels, MVars, locks ----

   Ownership rule. An object with rc > 0 belongs to one thread: its count is changed with
   plain arithmetic. Before a value crosses to another thread (a forked thread's closure,
   a message, an MVar's contents) the runtime marks everything reachable from it as
   shared (`wiz_mark_mt`: rc becomes -rc), and shared counts change atomically. rc == 0
   is immortal (hoisted constants), never counted. So a shared object only points to
   shared or immortal objects; in-place updates need rc == 1, which a shared object
   never has, and a shared thunk is forced under a lock and its value marked shared. */

#ifdef WIZ_NO_THREADS
/* one thread: nothing crosses to another, so nothing becomes shared */
static void wiz_mark_mt(wiz_val v) { (void)v; }
#else
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
#endif

/* Wait while `c` holds, on `cv` under `mu`. With WIZ_NO_THREADS no other thread can
   make `c` false, so waiting would never end: stop with `what` instead. */
#ifdef WIZ_NO_THREADS
#define WIZ_WAIT_WHILE(c, cv, mu, what) do { if (c) wiz_no_threads(what); } while (0)
#else
#define WIZ_WAIT_WHILE(c, cv, mu, what) while (c) pthread_cond_wait(cv, mu)
#endif

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
#ifdef WIZ_NO_THREADS
  (void)fn; (void)arg;
  wiz_no_threads("starting a thread");
#endif
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
#ifdef WIZ_NO_THREADS
  wiz_no_threads("Chan.fork");
#endif
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
  WIZ_WAIT_WHILE(!ch->head[side], &ch->cv, &ch->mu, "Chan.recv on an empty channel would wait forever");
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
  WIZ_WAIT_WHILE(!m->full, &m->cv, &m->mu, keep ? "MVar.read of an empty MVar would wait forever"
                                                : "MVar.take of an empty MVar would wait forever");
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
  WIZ_WAIT_WHILE(m->full, &m->cv, &m->mu, "MVar.put into a full MVar would wait forever");
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
  WIZ_WAIT_WHILE(l->held, &l->cv, &l->mu, "Lock.acquire of a held lock would wait forever");
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
#ifdef WIZ_NO_THREADS
  /* one thread: run on this one, with the stack it has */
  return wiz_main_thread(&args), args.rc;
#endif
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

/* ---- pure tasks (lib/Task.wiz, stage 31): `Task.spawn f` may compute `f ()` on another
   thread, `Task.get` waits for it ----

   A task is waiting to start (0), running (1) or done (2), under one mutex for all tasks
   (a task is coarse work; the lock is held only to change a state). Whoever moves a task
   from 0 to 1 runs it: its own thread, or the first `get` that needs it before any thread
   has started it (work-first), so `get` never waits for work nobody is doing and nested
   tasks can't deadlock. At most one task thread per online CPU runs at a time; a task
   spawned beyond that has no thread and runs at the `get` that needs it. A task's value
   is marked shared before it is published (another thread may `get` it). The task
   object (a foreign object) and its thread each hold a reference to the record. With
   WIZ_NO_THREADS, spawning stops with `wiz_no_threads` like `Chan.fork`. */

typedef struct {
  int state;    /* 0 waiting to start, 1 running, 2 done */
  int refs;     /* the Wiz object, and the thread if one was started */
  wiz_val fn;   /* `Unit → A`, shared; taken by whoever runs it */
  wiz_val val;  /* the value, shared, once done */
} wiz_task;

static pthread_mutex_t wiz_task_mu = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t wiz_task_cv = PTHREAD_COND_INITIALIZER;
static int64_t wiz_task_threads = 0; /* task threads running now */
static int64_t wiz_task_max = 0;     /* their limit: the online CPUs (0: not read yet) */

static void wiz_task_unref(wiz_task *t) {
  pthread_mutex_lock(&wiz_task_mu);
  int last = --t->refs == 0;
  pthread_mutex_unlock(&wiz_task_mu);
  if (!last) return;
  /* (outside the lock: dropping a value may finalise other tasks) */
  if (t->fn) wiz_dec(t->fn);
  if (t->state == 2) wiz_dec(t->val);
  free(t);
}
static void wiz_task_fin(void *p) { wiz_task_unref((wiz_task *)p); }

/* run a task this thread moved to state 1, and publish its value */
static void wiz_task_run(wiz_task *t) {
  wiz_val fn = t->fn;
  t->fn = 0;
  wiz_val u = WIZ_BOX(0);
  wiz_val v = wiz_apply(fn, 1, &u);
  wiz_mark_mt(v);
  pthread_mutex_lock(&wiz_task_mu);
  t->val = v;
  t->state = 2;
  pthread_cond_broadcast(&wiz_task_cv);
  pthread_mutex_unlock(&wiz_task_mu);
}

static void *wiz_task_thread(void *p) {
  wiz_task *t = (wiz_task *)p;
  pthread_mutex_lock(&wiz_task_mu);
  int mine = t->state == 0;
  if (mine) t->state = 1;
  pthread_mutex_unlock(&wiz_task_mu);
  if (mine) wiz_task_run(t);
  wiz_task_unref(t);
  pthread_mutex_lock(&wiz_task_mu);
  wiz_task_threads--;
  pthread_mutex_unlock(&wiz_task_mu);
  /* as wiz_thread_main: this thread's allocation balance, and one thread fewer */
  pthread_mutex_lock(&wiz_threads_mu);
  wiz_live_exited += wiz_live;
  wiz_threads_running--;
  pthread_cond_broadcast(&wiz_threads_cv);
  pthread_mutex_unlock(&wiz_threads_mu);
  return NULL;
}

/* give `t` a thread of its own if fewer than wiz_task_max are running; otherwise (or if
   the system has no thread to give) it waits for the `get` that needs it */
static void wiz_task_start(wiz_task *t) {
  pthread_mutex_lock(&wiz_task_mu);
  if (wiz_task_max == 0) {
    long n = sysconf(_SC_NPROCESSORS_ONLN);
    wiz_task_max = n > 0 ? n : 1;
  }
  int go = wiz_task_threads < wiz_task_max;
  if (go) { wiz_task_threads++; t->refs++; }
  pthread_mutex_unlock(&wiz_task_mu);
  if (!go) return;
  pthread_mutex_lock(&wiz_threads_mu);
  wiz_threads_running++;
  pthread_mutex_unlock(&wiz_threads_mu);
  const char *mb = getenv("WIZ_THREAD_STACK_MB");
  size_t size = (size_t)(mb ? atol(mb) : 256) << 20;
  pthread_attr_t attr;
  pthread_attr_init(&attr);
  pthread_attr_setstacksize(&attr, size);
  pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED);
  pthread_t th;
  int err = pthread_create(&th, &attr, wiz_task_thread, t);
  pthread_attr_destroy(&attr);
  if (err == 0) return;
  pthread_mutex_lock(&wiz_threads_mu);
  wiz_threads_running--;
  pthread_cond_broadcast(&wiz_threads_cv);
  pthread_mutex_unlock(&wiz_threads_mu);
  pthread_mutex_lock(&wiz_task_mu);
  wiz_task_threads--;
  t->refs--; /* the object's reference remains */
  pthread_mutex_unlock(&wiz_task_mu);
}

static wiz_task *wiz_task_of(wiz_val tv) { return (wiz_task *)((wiz_ext *)tv)->ptr; }

/* `Task.spawn f` */
WIZ_API wiz_val wiz_task_spawn(wiz_val fn) {
#ifdef WIZ_NO_THREADS
  (void)fn;
  wiz_no_threads("Task.spawn");
#endif
  wiz_task *t = (wiz_task *)calloc(1, sizeof(wiz_task));
  t->refs = 1;
  t->val = WIZ_BOX(0);
  wiz_mark_mt(fn);
  t->fn = fn;
  wiz_val tv = wiz_out_ptr(t, wiz_task_fin);
  wiz_task_start(t);
  return tv;
}

/* `Task.get t`: its value; runs it here if it hasn't started */
WIZ_API wiz_val wiz_task_get(wiz_val tv) {
  wiz_task *t = wiz_task_of(tv);
  pthread_mutex_lock(&wiz_task_mu);
  if (t->state == 0) {
    t->state = 1;
    pthread_mutex_unlock(&wiz_task_mu);
    wiz_task_run(t);
    pthread_mutex_lock(&wiz_task_mu);
  }
  WIZ_WAIT_WHILE(t->state != 2, &wiz_task_cv, &wiz_task_mu, "Task.get of a running task would wait forever");
  wiz_val v = t->val;
  wiz_inc(v);
  pthread_mutex_unlock(&wiz_task_mu);
  wiz_dec(tv);
  return v;
}

/* `Task.both f g`: `g ()` as a task while this thread runs `f ()`; the pair */
WIZ_API wiz_val wiz_task_both(wiz_val f, wiz_val g) {
#ifdef WIZ_NO_THREADS
  (void)f; (void)g;
  wiz_no_threads("Task.both");
#endif
  wiz_val tg = wiz_task_spawn(g);
  wiz_val u = WIZ_BOX(0);
  wiz_val a = wiz_apply(f, 1, &u);
  wiz_val b = wiz_task_get(tg);
  return wiz_pair(a, b);
}

/* `Task.race f g h`: the value of whichever finishes first (they are equal, `h`). If
   neither has a thread, `f ()` runs here. The other one runs on to its end. */
WIZ_API wiz_val wiz_task_race(wiz_val f, wiz_val g) {
#ifdef WIZ_NO_THREADS
  (void)f; (void)g;
  wiz_no_threads("Task.race");
#endif
  wiz_val tf = wiz_task_spawn(f), tg = wiz_task_spawn(g);
  wiz_task *a = wiz_task_of(tf), *b = wiz_task_of(tg);
  pthread_mutex_lock(&wiz_task_mu);
  wiz_val v;
  for (;;) {
    if (a->state == 2) { v = a->val; break; }
    if (b->state == 2) { v = b->val; break; }
    if (a->state == 0 && b->state == 0) {
      a->state = 1;
      pthread_mutex_unlock(&wiz_task_mu);
      wiz_task_run(a);
      pthread_mutex_lock(&wiz_task_mu);
      continue;
    }
    /* one of them is running (on its thread, or at another `get`): wait for a change */
    pthread_cond_wait(&wiz_task_cv, &wiz_task_mu);
  }
  wiz_inc(v);
  pthread_mutex_unlock(&wiz_task_mu);
  wiz_dec(tf);
  wiz_dec(tg);
  return v;
}
