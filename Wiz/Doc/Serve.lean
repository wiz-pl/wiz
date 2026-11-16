import Std.Data.HashMap
import Wiz.Socket
import Wiz.WebSocket

/-!
# A documentation server (`wiz doc --serve`)

`wiz doc` writes a static site; this serves that tree over HTTP on the loopback
interface, so that the pages can be progressively enhanced: a page made with `--serve`
carries `web/doc-live.js`, which asks a `wiz lsp --ws PORT` for the real type and doc of
a declaration (`--lsp PORT`) and shows them in a panel.

The server has two routes:

* `/` and `/NAME` — files under the generated tree (`/` is `index.html`); only `GET`,
  no request body, `.` and `..` refused.
* `/sources/NAME.wiz` — a documented module's source, kept in memory from the `wiz doc`
  run. The client opens it in the language server (`textDocument/didOpen` with the whole
  text), which is what gives the page's declarations positions to ask about.

It is a development server, not a publishing one: loopback only, one request per
connection (`Connection: close`), no TLS, no authentication, no caching.

The HTTP framing is the WebSocket handshake's: `Wiz/WebSocket.lean`'s `readHead` reads a
request's first line and headers, and the response is written with a `Content-Length`
and a `Connection: close`.
-/

namespace Wiz.Doc.Serve

/-- What is served: the generated tree, and the documented modules' sources by name. -/
structure Site where
  root : System.FilePath
  /-- module name → its source (served at `sources/<name>.wiz`) -/
  sources : Std.HashMap String String := {}

/-- A file's media type, by extension. -/
def contentType (file : System.FilePath) : String :=
  match file.extension with
  | some "html" | some "htm" => "text/html; charset=utf-8"
  | some "js" | some "mjs" => "text/javascript; charset=utf-8"
  | some "css" => "text/css; charset=utf-8"
  | some "json" => "application/json; charset=utf-8"
  | some "wasm" => "application/wasm"
  | some "svg" => "image/svg+xml"
  | some "png" => "image/png"
  | some "ico" => "image/x-icon"
  | some "map" => "application/json"
  | some "txt" => "text/plain; charset=utf-8"
  | _ => "application/octet-stream"

/-- A request target (`/a/b.html?x=1`) as safe path segments: no query, no `.` or `..`,
no backslash. `none` if it tries to leave the root. -/
def segments (target : String) : Option (List String) := do
  let path := (target.splitOn "?").headD ""
  let segs := (path.splitOn "/").filter (· != "")
  if segs.any (fun s => s == "." || s == ".." || s.contains '\\') then none
  pure segs

/-- A file of the generated tree (`rel` is a `/`-separated path inside it), read whole. -/
def serveFile (site : Site) (rel : String) : IO (Option (String × ByteArray)) := do
  let file := (rel.splitOn "/").foldl (fun p s => p / s) site.root
  if !(← file.pathExists) || (← file.isDir) then return none
  let body ← try some <$> IO.FS.readBinFile file catch _ => pure none
  pure (body.map fun b => (contentType file, b))

/-- The body of a request's path, and its media type: a file under the site, a module
source, or `none` (404). -/
def lookup (site : Site) (target : String) : IO (Option (String × ByteArray)) := do
  let some segs ← pure (segments target) | return none
  match segs with
  | [] => serveFile site "index.html"
  | ["sources", name] =>
    if !name.endsWith ".wiz" then return none
    let module := (name.dropEnd 4).toString
    match site.sources.get? module with
    | some src => pure (some ("text/plain; charset=utf-8", src.toUTF8))
    | none => pure none
  | _ => serveFile site (String.intercalate "/" segs)

/-- Answer with a status line, the media type, the body and `Connection: close`. -/
def respond (w : IO.FS.Stream) (status : String) (mime : String) (body : ByteArray) : IO Unit := do
  w.putStr (s!"HTTP/1.1 {status}\r\nContent-Type: {mime}\r\nContent-Length: {body.size}\r\n" ++
    "Cache-Control: no-cache\r\nConnection: close\r\n\r\n")
  w.write body
  w.flush

/-- One connection: a request (`GET` only), then its answer. -/
def handle (site : Site) (r w : IO.FS.Handle) : IO Unit := do
  let rs := IO.FS.Stream.ofHandle r
  let ws := IO.FS.Stream.ofHandle w
  let some (line, _) ← WebSocket.readHead rs | return
  unless line.startsWith "GET " do
    respond ws "405 Method Not Allowed" "text/plain; charset=utf-8" "only GET\n".toUTF8
    return
  -- `GET /name?query HTTP/1.1`
  let target := ((line.drop 4).toString.splitOn " ").headD ""
  match ← lookup site target with
  | some (mime, body) => respond ws "200 OK" mime body
  | none => respond ws "404 Not Found" "text/plain; charset=utf-8" "not found\n".toUTF8

/-- Accept connections until the listening descriptor is closed. -/
partial def acceptLoop (fd : UInt32) (site : Site) : IO Unit := do
  match ← (try some <$> Socket.accept fd catch _ => pure none) with
  | none => pure ()
  | some (_, r, w) =>
    let _ ← IO.asTask (prio := .dedicated) (try handle site r w catch _ => pure ())
    acceptLoop fd site

/-- Listen on `127.0.0.1:port` (`port` 0: a free one); the descriptor and the port. -/
def listen (_site : Site) (port : UInt16) : IO (UInt32 × UInt16) :=
  Socket.tcpListen Socket.loopback port

end Wiz.Doc.Serve
