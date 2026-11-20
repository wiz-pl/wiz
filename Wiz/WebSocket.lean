/-!
# WebSockets (RFC 6455), for `wiz lsp --ws PORT`

A browser cannot open a Unix socket, or a plain TCP connection: it speaks WebSockets.
The protocol is small enough to write here, over the blocking handles of
`Wiz/Socket.lean`:

* **The handshake.** The client sends an HTTP `GET` with `Upgrade: websocket` and a
  random `Sec-WebSocket-Key`; the server answers `101 Switching Protocols` with
  `Sec-WebSocket-Accept: base64(SHA-1(key ++ GUID))` (so a server that doesn't speak
  WebSockets can't be mistaken for one). Before that the server checks the `Origin`
  header: a page on any web site can open a WebSocket to `127.0.0.1`, so only local
  pages (and clients that send no `Origin`, which browsers always do) are let in.
* **The token** (#430). The `Origin` check stops web pages, not local programs (they
  simply leave the header out), so the upgrade must also carry the server's token: as
  `?token=…` in the request target (what a browser can send) or as
  `Authorization: Bearer …`. A missing or wrong token gets `401` before any `101`; the
  comparison takes the same time wherever the first difference is.
* **Frames.** After the handshake both sides send frames: a byte with the final-fragment
  bit and the opcode (text 1, binary 2, continuation 0, close 8, ping 9, pong 10), the
  payload length (7 bits, or 126 + 16 bits, or 127 + 64 bits), and, from the client
  only, a 4-byte mask that is XORed over the payload. A message may be split into
  fragments; control frames may come between them.

The language server sends one JSON-RPC message per text frame (no `Content-Length`).
-/

namespace Wiz.WebSocket

/-! ## SHA-1 and base64 (for the handshake only) -/

private def rotl (x : UInt32) (n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))

/-- SHA-1 (FIPS 180-4). Broken as a hash for security, but it is what RFC 6455 uses. -/
def sha1 (msg : ByteArray) : ByteArray := Id.run do
  let bits := msg.size * 8
  let mut m := msg.push 0x80
  while m.size % 64 != 56 do m := m.push 0
  for i in [0:8] do m := m.push ((bits >>> (8 * (7 - i))) % 256).toUInt8
  let mut h : Array UInt32 := #[0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0]
  for chunk in [0:m.size / 64] do
    let mut w : Array UInt32 := Array.mkEmpty 80
    for i in [0:16] do
      let byte (j : Nat) : UInt32 := (m.get! (chunk * 64 + 4 * i + j)).toUInt32
      w := w.push ((byte 0 <<< 24) ||| (byte 1 <<< 16) ||| (byte 2 <<< 8) ||| byte 3)
    for i in [16:80] do
      w := w.push (rotl (w[i-3]! ^^^ w[i-8]! ^^^ w[i-14]! ^^^ w[i-16]!) 1)
    let mut a := h[0]!
    let mut b := h[1]!
    let mut c := h[2]!
    let mut d := h[3]!
    let mut e := h[4]!
    for i in [0:80] do
      let (f, k) : UInt32 × UInt32 :=
        if i < 20 then ((b &&& c) ||| ((~~~b) &&& d), 0x5A827999)
        else if i < 40 then (b ^^^ c ^^^ d, 0x6ED9EBA1)
        else if i < 60 then ((b &&& c) ||| (b &&& d) ||| (c &&& d), 0x8F1BBCDC)
        else (b ^^^ c ^^^ d, 0xCA62C1D6)
      let t := rotl a 5 + f + e + k + w[i]!
      e := d
      d := c
      c := rotl b 30
      b := a
      a := t
    h := #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e]
  let mut out := ByteArray.empty
  for x in h do
    for s in [24, 16, 8, 0] do out := out.push (x >>> s.toUInt32).toUInt8
  pure out

def base64 (bs : ByteArray) : String := Id.run do
  let abc := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.toArray
  let mut out := ""
  let mut i := 0
  while i < bs.size do
    let n := bs.size - i
    let b0 := (bs.get! i).toNat
    let b1 := if n > 1 then (bs.get! (i + 1)).toNat else 0
    let b2 := if n > 2 then (bs.get! (i + 2)).toNat else 0
    let x := (b0 <<< 16) ||| (b1 <<< 8) ||| b2
    out := out.push abc[(x >>> 18) % 64]!
    out := out.push abc[(x >>> 12) % 64]!
    out := out.push (if n > 1 then abc[(x >>> 6) % 64]! else '=')
    out := out.push (if n > 2 then abc[x % 64]! else '=')
    i := i + 3
  pure out

/-- The `Sec-WebSocket-Accept` answering a `Sec-WebSocket-Key`. -/
def acceptKey (key : String) : String :=
  base64 (sha1 (key ++ "258EAFA5-E914-47DA-95CA-C5AB0DC85B11").toUTF8)

/-! ## The handshake -/

/-- Read the header lines of an HTTP message, up to the blank line: the first line, and
the headers with lower-case names. `none` if the stream ends first, or the message is
unreasonably long. -/
def readHead (r : IO.FS.Stream) : IO (Option (String × List (String × String))) := do
  let first ← r.getLine
  if first.isEmpty then return none
  let mut headers := []
  for _ in [0:100] do
    let line ← r.getLine
    if line.isEmpty then return none
    let line := line.trimAscii.toString
    if line.isEmpty then return some (first.trimAscii.toString, headers.reverse)
    match line.splitOn ":" with
    | k :: v => headers := (k.trimAscii.toString.toLower, (":".intercalate v).trimAscii.toString) :: headers
    | [] => pure ()
  pure none

/-- Origins let in: pages on this machine (`http://localhost:…`, `http://127.0.0.1:…`,
`http://[::1]:…`, and `https` alike), local files (browsers say `null`), and editor
webviews (`vscode-webview://…`). -/
def localOrigin (origin : String) : Bool :=
  origin == "null" || origin.startsWith "vscode-webview://" ||
  ["http://", "https://"].any fun scheme =>
    origin.startsWith scheme &&
      let host := (origin.drop scheme.length).toString
      ["localhost", "127.0.0.1", "[::1]"].any fun h =>
        host == h || host.startsWith (h ++ ":")

/-! ## The token (#430) -/

/-- Lower-case hexadecimal. -/
def hex (bs : ByteArray) : String := Id.run do
  let digits := "0123456789abcdef".toList.toArray
  let mut out := ""
  for b in bs do
    out := out.push digits[(b >>> 4).toNat]!
    out := out.push digits[(b &&& 15).toNat]!
  pure out

/-- A fresh token: 128 random bits, in hex. -/
def freshToken : IO String := do
  pure (hex (← IO.getRandomBytes 16))

/-- Equal strings, compared in a time that depends only on the lengths (not on where the
first difference is), so a client can't find the token a byte at a time. -/
def constantTimeEq (a b : String) : Bool := Id.run do
  let (x, y) := (a.toUTF8, b.toUTF8)
  if x.size != y.size then return false
  let mut acc : UInt8 := 0
  for i in [0:x.size] do
    acc := acc ||| (x.get! i ^^^ y.get! i)
  pure (acc == 0)

/-- The value of `name` in a request target's query (`/path?a=1&token=…`), if any. -/
def queryParam (target name : String) : Option String :=
  match target.splitOn "?" with
  | _ :: q :: _ =>
    (q.splitOn "&").findSome? fun kv =>
      match kv.splitOn "=" with
      | k :: v => if k == name then some ("=".intercalate v) else none
      | [] => none
  | _ => none

/-- The token a request presents: `?token=…` in its target, or `Authorization: Bearer …`. -/
def presentedToken (target : String) (headers : List (String × String)) : Option String :=
  match queryParam target "token" with
  | some t => some t
  | none => do
    let a ← headers.lookup "authorization"
    let a := a.trimAscii.toString
    if a.toLower.startsWith "bearer " then some (a.drop 7).trimAscii.toString else none

/-- (11w) The files of the web infoview a server may hand out over HTTP (`web/build.sh`'s
output), with their media types: only these, by exact name, so no other file is reachable.
The page's language client is the playground's (`web/playground-lsp.js`), so its modules are
served too. -/
def webAssets : List (String × String) :=
  [("infoview.html", "text/html; charset=utf-8"), ("infoview.js", "text/javascript; charset=utf-8"),
   -- (11s) the parts infoview.js shares with the playground and the documentation's pages
   ("playground-lsp.js", "text/javascript; charset=utf-8"),
   ("lsp-client.js", "text/javascript; charset=utf-8"),
   ("goals.js", "text/javascript; charset=utf-8"),
   ("tagged.js", "text/javascript; charset=utf-8"),
   -- the editor's overlays (squiggles, completions, hover), their layout, and the
   -- text-input helper the completion widget imports
   ("squiggles.js", "text/javascript; charset=utf-8"),
   ("completions.js", "text/javascript; charset=utf-8"),
   ("hover.js", "text/javascript; charset=utf-8"),
   ("framework/editor-text.js", "text/javascript; charset=utf-8"),
   ("overlays.css", "text/css; charset=utf-8"),
   ("wiz-infoview.mjs", "text/javascript; charset=utf-8"), ("wiz-infoview.wasm", "application/wasm")]

/-- The server's half of the handshake on a new connection: `true` if it is a WebSocket
now. A request that is not a WebSocket upgrade, or comes from another origin
(`localOrigin`), gets an HTTP error and `false`. (#430) With `token`, an upgrade that
does not present it (`presentedToken`) gets `401 Unauthorized` and `false`; `none` lets
every local client in (`wiz lsp --ws-insecure` only). (11w) With `web` (the directory of
the web infoview), a plain `GET` of one of `webAssets` (`/infoview.html?…`) gets that file
and `false`, with or without a token (the files are the toolchain's own, the same for
everyone); any other path gets `404`. -/
def accept (r w : IO.FS.Stream) (token : Option String) (web : Option String := none) : IO Bool := do
  let refuse (status : String) : IO Bool := do
    w.putStr s!"HTTP/1.1 {status}\r\nContent-Length: 0\r\nConnection: close\r\n\r\n"
    w.flush
    pure false
  let some (line, headers) ← readHead r | return ← refuse "400 Bad Request"
  let get (k : String) := (headers.lookup k).getD ""
  unless line.startsWith "GET " do return ← refuse "405 Method Not Allowed"
  if let some o := headers.lookup "origin" then
    unless localOrigin o do return ← refuse "403 Forbidden"
  let key := get "sec-websocket-key"
  -- `GET /name?query HTTP/1.1`
  let target := ((line.drop 4).toString.splitOn " ").headD ""
  unless (get "upgrade").toLower == "websocket" && !key.isEmpty do
    let some dir := web | return ← refuse "426 Upgrade Required"
    let path : String := (target.splitOn "?").headD ""
    let name := if path.startsWith "/" then (path.drop 1).toString else path
    let name := if name.isEmpty then "infoview.html" else name
    let some (_, mime) := webAssets.find? (·.1 == name) | return ← refuse "404 Not Found"
    let some body ← (try some <$> IO.FS.readBinFile (dir ++ "/" ++ name) catch _ => pure none)
      | return ← refuse "404 Not Found"
    w.putStr (s!"HTTP/1.1 200 OK\r\nContent-Type: {mime}\r\nContent-Length: {body.size}\r\n" ++
      "Cache-Control: no-cache\r\nConnection: close\r\n\r\n")
    w.write body
    w.flush
    return false
  if let some t := token then
    let ok := match presentedToken target headers with
      | some p => constantTimeEq p t
      | none => false
    unless ok do return ← refuse "401 Unauthorized"
  w.putStr ("HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n" ++
    s!"Sec-WebSocket-Accept: {acceptKey key}\r\n\r\n")
  w.flush
  pure true

/-- The client's half (for tests and command-line clients): send the upgrade request for
`path` on `host`, check the answer. `bearer`: a token, sent as `Authorization: Bearer`
(a token in `path`'s query works too). -/
def connect (r w : IO.FS.Stream) (host : String) (path : String := "/") (origin : Option String := none)
    (bearer : Option String := none) : IO (Except String Unit) := do
  let key := "dGhlIHNhbXBsZSBub25jZQ=="
  let originLine := match origin with | some o => s!"Origin: {o}\r\n" | none => ""
  let authLine := match bearer with | some t => s!"Authorization: Bearer {t}\r\n" | none => ""
  w.putStr (s!"GET {path} HTTP/1.1\r\nHost: {host}\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n" ++
    s!"Sec-WebSocket-Key: {key}\r\nSec-WebSocket-Version: 13\r\n{originLine}{authLine}\r\n")
  w.flush
  let some (line, headers) ← readHead r | return .error "the connection closed during the handshake"
  unless (line.splitOn " ")[1]? == some "101" do return .error line
  unless headers.lookup "sec-websocket-accept" == some (acceptKey key) do return .error "wrong Sec-WebSocket-Accept"
  pure (.ok ())

/-! ## Frames -/

def opText : UInt8 := 1
def opBinary : UInt8 := 2
def opClose : UInt8 := 8
def opPing : UInt8 := 9
def opPong : UInt8 := 10

/-- Messages longer than this are refused (the connection is closed). -/
def maxMessage : Nat := 1 <<< 28

structure Frame where
  fin : Bool
  op : UInt8
  payload : ByteArray

/-- Exactly `n` bytes, or `none` at the end of the stream. -/
partial def readExact (r : IO.FS.Stream) (n : Nat) (acc : ByteArray := .empty) : IO (Option ByteArray) := do
  if acc.size ≥ n then return some acc
  let bs ← r.read (n - acc.size).toUSize
  if bs.isEmpty then return none
  readExact r n (acc ++ bs)

private def bigEndian (bs : ByteArray) : Nat := bs.foldl (fun n b => n * 256 + b.toNat) 0

/-- Read one frame. A server (`masked := true`) requires the client's mask, a client
requires its absence (RFC 6455 §5.1); `none` at the end of the stream, or on a frame that
breaks these rules or is too long. -/
def readFrame (r : IO.FS.Stream) (masked : Bool) : IO (Option Frame) := do
  let some hd ← readExact r 2 | return none
  let fin := hd.get! 0 &&& 0x80 != 0
  let op := hd.get! 0 &&& 0x0f
  if (hd.get! 1 &&& 0x80 != 0) != masked then return none
  let len7 := (hd.get! 1 &&& 0x7f).toNat
  let extra := if len7 == 126 then 2 else if len7 == 127 then 8 else 0
  let some ext ← readExact r extra | return none
  let len := if extra == 0 then len7 else bigEndian ext
  if len > maxMessage then return none
  let mask ← if masked then readExact r 4 else pure (some .empty)
  let some mask := mask | return none
  let some payload ← readExact r len | return none
  let payload := if masked then
      (payload.toList.zipIdx.map fun (b, i) => b ^^^ mask.get! (i % 4)).toByteArray
    else payload
  pure (some { fin, op, payload })

/-- A frame's bytes (`mask`: a client's 4-byte mask). -/
def frameBytes (op : UInt8) (payload : ByteArray) (mask : Option ByteArray := none) : ByteArray := Id.run do
  let n := payload.size
  let mbit : UInt8 := if mask.isSome then 0x80 else 0
  let mut out := ByteArray.empty.push (0x80 ||| op)
  if n < 126 then out := out.push (mbit ||| n.toUInt8)
  else if n < 65536 then out := (out.push (mbit ||| 126)).push (n >>> 8).toUInt8 |>.push n.toUInt8
  else
    out := out.push (mbit ||| 127)
    for i in [0:8] do out := out.push (n >>> (8 * (7 - i))).toUInt8
  match mask with
  | none => out ++ payload
  | some m => out ++ m ++ (payload.toList.zipIdx.map fun (b, i) => b ^^^ m.get! (i % 4)).toByteArray

/-- Send one frame (in one write, so that frames written by two threads don't mix). -/
def writeFrame (w : IO.FS.Stream) (op : UInt8) (payload : ByteArray) (mask : Option ByteArray := none) : IO Unit := do
  w.write (frameBytes op payload mask)
  w.flush

/-- Send a text message. -/
def sendText (w : IO.FS.Stream) (text : String) (mask : Option ByteArray := none) : IO Unit :=
  writeFrame w opText text.toUTF8 mask

/-- Read the next data message (text or binary, its fragments joined), answering pings on
the way. `none` when the peer closes (its close frame is answered), the stream ends, or
the peer breaks the protocol. `server`: this end is the server (frames come masked). -/
partial def recv (r w : IO.FS.Stream) (server : Bool := true) (acc : Option ByteArray := none) : IO (Option ByteArray) := do
  let mask : Option ByteArray := if server then none else some (ByteArray.mk #[1, 2, 3, 4])
  let some f ← readFrame r server | return none
  if f.op == opClose then
    try writeFrame w opClose (f.payload.extract 0 2) mask catch _ => pure ()
    return none
  if f.op == opPing then
    writeFrame w opPong f.payload mask
    return ← recv r w server acc
  if f.op == opPong then return ← recv r w server acc
  -- data: a first fragment (text/binary) or a continuation of one
  let acc ← match acc, f.op with
    | none, 1 | none, 2 => pure f.payload
    | some a, 0 => pure (a ++ f.payload)
    | _, _ => return none
  if acc.size > maxMessage then return none
  if f.fin then pure (some acc) else recv r w server (some acc)

/-- Read the next message as text (`none` also if it is not UTF-8). -/
def recvText (r w : IO.FS.Stream) (server : Bool := true) : IO (Option String) := do
  let some bs ← recv r w server | return none
  pure (String.fromUTF8? bs)

end Wiz.WebSocket
