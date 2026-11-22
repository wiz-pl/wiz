/-!
# Unix-domain and TCP sockets

Lean's library has no Unix-domain sockets, which `wiz lsp --infoview SOCK` needs, and its
TCP sockets are asynchronous (libuv) where the server wants blocking handles
(`wiz lsp --ws PORT`, `Wiz/WebSocket.lean`). The few calls they use are in `c/sockets.c` (which the
linker compiles into every executable, see the lakefile); a connection comes back as a
pair of ordinary handles, one to read and one to write. The C side cannot read Lean
objects (it is compiled without Lean's headers), so paths go to it a byte at a time and
it builds its results with the functions exported here.
-/

namespace Wiz.Socket

/-! The C side's results. -/
@[export wiz_sock_ok_unit] def okUnit : IO Unit := pure ()
@[export wiz_sock_ok_fd] def okFd (fd : UInt32) : IO UInt32 := pure fd
@[export wiz_sock_ok_conn] def okConn (fd : UInt32) (r w : IO.FS.Handle) : IO (UInt32 × IO.FS.Handle × IO.FS.Handle) :=
  pure (fd, r, w)
@[export wiz_sock_ok_handles] def okHandles (r w : IO.FS.Handle) : IO (IO.FS.Handle × IO.FS.Handle) := pure (r, w)
@[export wiz_sock_ok_pair] def okPair (r₀ w₀ r₁ w₁ : IO.FS.Handle) :
    IO ((IO.FS.Handle × IO.FS.Handle) × (IO.FS.Handle × IO.FS.Handle)) := pure ((r₀, w₀), (r₁, w₁))
@[export wiz_sock_error] def error (e : IO.Error) : IO Unit := throw e

@[extern "wiz_sock_path_clear"] opaque pathClear : IO Unit
@[extern "wiz_sock_path_push"] opaque pathPush (b : UInt8) : IO Unit
@[extern "wiz_unix_listen"] opaque listenRaw : IO UInt32
@[extern "wiz_unix_connect"] opaque connectRaw : IO (IO.FS.Handle × IO.FS.Handle)
@[extern "wiz_unix_close"] opaque closeRaw (fd : UInt32) : IO Unit

/-- Hand the socket path to the C side. -/
def setPath (path : String) : IO Unit := do
  pathClear
  for b in path.toUTF8 do pathPush b

/-- Listen on the socket file `path` (replacing a stale one); the listening descriptor. -/
def listen (path : String) : IO UInt32 := do setPath path; listenRaw

@[extern "wiz_unix_mode"] opaque modeRaw : IO UInt32

/-- The permission bits (`st_mode & 0777`) of the socket file `path`. The listener creates
    it owner-only; this is for the test that checks the mode. -/
def mode (path : String) : IO UInt32 := do setPath path; modeRaw

/-- Wait for a connection (on a Unix or TCP socket): its descriptor (for `shutdown`), and its read and write handles. -/
@[extern "wiz_unix_accept"] opaque accept (fd : UInt32) : IO (UInt32 × IO.FS.Handle × IO.FS.Handle)

/-- Connect to the socket file `path`: read and write handles. -/
def connect (path : String) : IO (IO.FS.Handle × IO.FS.Handle) := do setPath path; connectRaw

@[extern "wiz_tcp_listen"] opaque tcpListenRaw (addr : UInt32) (port : UInt16) : IO UInt32
@[extern "wiz_tcp_port"] opaque tcpPortRaw (fd : UInt32) : IO UInt32
@[extern "wiz_tcp_connect"] opaque tcpConnect (addr : UInt32) (port : UInt16) : IO (IO.FS.Handle × IO.FS.Handle)
/-- Stop listening on a TCP socket. -/
@[extern "wiz_fd_close"] opaque closeFd (fd : UInt32) : IO Unit

/-- 127.0.0.1, as `tcpListen` takes addresses (host byte order). -/
def loopback : UInt32 := 0x7f000001

/-- An IPv4 address `a.b.c.d`, as `tcpListen` takes it. -/
def parseIPv4 (s : String) : Option UInt32 :=
  match s.splitOn "." |>.mapM (·.toNat?) with
  | some [a, b, c, d] =>
    if [a, b, c, d].all (· < 256) then some (((a * 256 + b) * 256 + c) * 256 + d).toUInt32 else none
  | _ => none

/-- Listen on TCP `addr`:`port` (`port` 0: a free one): the listening descriptor and the
port. -/
def tcpListen (addr : UInt32) (port : UInt16) : IO (UInt32 × UInt16) := do
  let fd ← tcpListenRaw addr port
  pure (fd, (← tcpPortRaw fd).toUInt16)

/-- Two connected sockets, each as (read, write) handles. -/
@[extern "wiz_socket_pair"] opaque pair : IO ((IO.FS.Handle × IO.FS.Handle) × (IO.FS.Handle × IO.FS.Handle))

/-- Shut a connection down (a thread reading it sees the end of the stream). -/
@[extern "wiz_fd_shutdown"] opaque shutdown (fd : UInt32) : IO Unit

/-- Stop listening on `fd` and remove the socket file `path`. -/
def close (fd : UInt32) (path : String) : IO Unit := do setPath path; closeRaw fd

end Wiz.Socket

namespace Wiz

@[extern "wiz_exit_on_panic"] private opaque exitOnPanicRaw (flag : Bool) : IO Unit

/-- From now on, a `panic!` anywhere in this process (the kernel's evaluator on an
ill-typed value, an index out of range) ends it with status 1, after its message, instead
of going on with the type's default value. The batch commands (`wiz check`, `build`,
`run`) set it: a kernel-internal failure must fail the check, never become a value (the
default used to be `Sort 0`, a well-formed term: `absurd` on a glued value panicked and a
type became `Prop`, F2). The language server does not (it must survive), and relies
on the default value being a stuck unknown (`Val`'s `Inhabited` instance). -/
def exitOnPanic (flag : Bool := true) : IO Unit := exitOnPanicRaw flag

end Wiz
