// A stand-in language server for the playground's tests: a small WebSocket server that
// implements just enough of the contract in `docs/playground-lsp.md` — `initialize`
// (with the `wizInfoview` capability), `initialized`, full-text `didOpen`/`didChange`,
// `publishDiagnostics`, and the Wiz infoview requests (`wiz/interactiveGoals`,
// `wiz/plainGoal`, `wiz/interactiveTermGoal`, `wiz/plainTermGoal`, `wiz/subtermInfo`).
// `mode: "plain"` answers the interactive methods with `MethodNotFound`, for the
// fallback test.
//
// No dependency: `http` plus the RFC 6455 frames in `web/ws_frames.mjs`.
//
//   node web/mock_lsp_server.mjs [PORT]        # prints the URL, runs until killed
//
// In a test: `const mock = await startMockServer(); …; await mock.close();`
"use strict";
import http from "node:http";
import { pathToFileURL } from "node:url";
import { acceptKey, encodeFrame, FrameReader, OPCODE } from "./ws_frames.mjs";

// The fixture program the goal ranges below refer to (0-based LSP lines).
export const FIXTURE_TEXT = `import Prelude
def k : Nat → Bool → Nat := by
  intro n
  intro b
  exact n
`;

const INFOVIEW_METHODS = [
  "wiz/plainGoal", "wiz/plainTermGoal", "wiz/interactiveGoals",
  "wiz/interactiveTermGoal", "wiz/subtermInfo", "wiz/interactiveInfo",
];

const nat = (range) => ({
  tag: [{ ref: 5, kind: "const", name: "Nat", ...(range ? { range } : {}) }, { text: "Nat" }],
});
const bool = (range) => ({
  tag: [{ ref: 6, kind: "const", name: "Bool", ...(range ? { range } : {}) }, { text: "Bool" }],
});
const sort = () => ({ tag: [{ ref: 1, kind: "sort" }, { text: "Type" }] });

function goalResult(session) {
  return {
    session,
    range: { start: { line: 1, character: 28 }, end: { line: 4, character: 9 } },
    messages: [],
    goals: [{
      userName: null,
      goalPrefix: "⊢ ",
      hyps: [
        {
          names: ["n"], val: null,
          range: { start: { line: 2, character: 8 }, end: { line: 2, character: 9 } },
          type: nat({ start: { line: 2, character: 8 }, end: { line: 2, character: 9 } }),
        },
        {
          names: ["b"], val: null,
          range: { start: { line: 3, character: 8 }, end: { line: 3, character: 9 } },
          type: bool({ start: { line: 3, character: 8 }, end: { line: 3, character: 9 } }),
        },
      ],
      type: nat({ start: { line: 1, character: 21 }, end: { line: 1, character: 23 } }),
    }],
    // The optional extension: the term/syntax at the cursor, as tagged text.
    tree: {
      tag: [{ ref: 9, kind: "app" }, {
        append: [
          { tag: [{ ref: 10, kind: "const", name: "Nat.add" }, { text: "Nat.add" }] },
          { text: " " },
          { tag: [{ ref: 11, kind: "var", name: "n" }, { text: "n" }] },
          { text: " " },
          { tag: [{ ref: 12, kind: "lit" }, { text: "1" }] },
        ],
      }],
    },
  };
}

function plainGoalResult() {
  return {
    goals: ["n : Nat\nb : Bool\n⊢ Nat"],
    rendered: "```wiz\nn : Nat\nb : Bool\n⊢ Nat\n```",
    messages: [],
  };
}

function termResult(session) {
  return {
    session,
    range: { start: { line: 1, character: 21 }, end: { line: 1, character: 23 } },
    goal: { userName: null, goalPrefix: "⊢ ", hyps: [], type: nat() },
  };
}

function plainTermResult() {
  return {
    goal: "⊢ Nat",
    range: { start: { line: 1, character: 21 }, end: { line: 1, character: 23 } },
  };
}

function diagnosticsFor(text) {
  if (!/(BAD|nope)/.test(text || "")) return [];
  return [{
    range: { start: { line: 0, character: 0 }, end: { line: 0, character: 3 } },
    severity: 1,
    source: "wiz-mock",
    code: "unknown-identifier",
    message: "mock: unknown identifier",
  }];
}

export async function startMockServer(options = {}) {
  const mode = options.mode || "full";
  const stats = {
    connections: 0, initialize: 0, initialized: 0,
    didOpen: 0, didChange: 0, requests: 0, diagnostics: 0,
  };
  const docs = new Map();
  const clients = new Set();
  const server = http.createServer((req, res) => {
    res.writeHead(426, { "content-type": "text/plain", upgrade: "websocket" });
    res.end("this is a WebSocket server\n");
  });

  const send = (client, message) => {
    if (!client.socket.destroyed) {
      client.socket.write(encodeFrame(OPCODE.text, Buffer.from(JSON.stringify(message), "utf8")));
    }
  };
  const reply = (client, id, result) => send(client, { jsonrpc: "2.0", id, result });
  const replyError = (client, id, code, message) =>
    send(client, { jsonrpc: "2.0", id, error: { code, message } });
  const publish = (client, uri, text) => {
    const diagnostics = diagnosticsFor(text);
    stats.diagnostics += 1;
    send(client, {
      jsonrpc: "2.0", method: "textDocument/publishDiagnostics",
      params: { uri, diagnostics },
    });
  };

  function handle(client, message) {
    const method = message.method;
    const id = message.id;
    const params = message.params || {};
    if (typeof method !== "string") return;
    stats.requests += 1;
    const isRequest = id !== undefined && id !== null;
    switch (method) {
      case "initialize":
        stats.initialize += 1;
        reply(client, id, {
          capabilities: {
            textDocumentSync: 1,
            experimental: { wizInfoview: { version: 1, methods: INFOVIEW_METHODS.slice() } },
          },
          serverInfo: { name: "wiz-mock", version: "0.0.1" },
        });
        return;
      case "initialized":
        stats.initialized += 1;
        return;
      case "textDocument/didOpen": {
        stats.didOpen += 1;
        const td = params.textDocument || {};
        docs.set(td.uri, { text: td.text || "", version: td.version || 1 });
        client.session += 1;
        publish(client, td.uri, td.text);
        return;
      }
      case "textDocument/didChange": {
        stats.didChange += 1;
        const td = params.textDocument || {};
        const changes = Array.isArray(params.contentChanges) ? params.contentChanges : [];
        const text = changes.length ? (changes[changes.length - 1].text || "") : "";
        docs.set(td.uri, { text, version: td.version || 1 });
        client.session += 1;
        publish(client, td.uri, text);
        return;
      }
      case "textDocument/didClose":
        docs.delete((params.textDocument || {}).uri);
        return;
      case "wiz/interactiveGoals":
        if (mode === "plain") return replyError(client, id, -32601, "MethodNotFound");
        return reply(client, id, goalResult(client.session));
      case "wiz/plainGoal":
        return reply(client, id, plainGoalResult());
      case "wiz/interactiveTermGoal":
        if (mode === "plain") return replyError(client, id, -32601, "MethodNotFound");
        return reply(client, id, termResult(client.session));
      case "wiz/plainTermGoal":
        return reply(client, id, plainTermResult());
      case "wiz/subtermInfo":
        if (mode === "plain") return replyError(client, id, -32601, "MethodNotFound");
        return reply(client, id, {
          text: "Nat", kind: "const", name: "Nat", session: client.session,
          type: sort(),
          definition: {
            uri: "file:///lib/Prelude.wiz",
            range: { start: { line: 6, character: 0 }, end: { line: 6, character: 9 } },
          },
        });
      case "wiz/interactiveInfo":
        if (mode === "plain") return replyError(client, id, -32601, "MethodNotFound");
        return reply(client, id, { items: [], session: client.session });
      case "shutdown":
        return reply(client, id, null);
      case "exit":
        client.socket.end();
        return;
      default:
        if (isRequest) replyError(client, id, -32601, "MethodNotFound: " + method);
        return;
    }
  }

  server.on("upgrade", (req, socket) => {
    const key = req.headers["sec-websocket-key"];
    if (!key || String(req.headers.upgrade || "").toLowerCase() !== "websocket") {
      socket.write("HTTP/1.1 400 Bad Request\r\n\r\n");
      socket.destroy();
      return;
    }
    socket.write(
      "HTTP/1.1 101 Switching Protocols\r\n" +
      "Upgrade: websocket\r\n" +
      "Connection: Upgrade\r\n" +
      `Sec-WebSocket-Accept: ${acceptKey(key)}\r\n` +
      "\r\n");
    const client = { socket, session: 0, reader: new FrameReader() };
    stats.connections += 1;
    clients.add(client);
    socket.on("data", (chunk) => {
      let frames;
      try {
        frames = client.reader.push(chunk);
      } catch (e) {
        socket.destroy();
        return;
      }
      for (const frame of frames) {
        if (frame.opcode === OPCODE.text || frame.opcode === OPCODE.binary) {
          let message;
          try {
            message = JSON.parse(frame.payload.toString("utf8"));
          } catch (_) {
            continue;
          }
          try {
            handle(client, message);
          } catch (e) {
            // A bad message must not take the server down.
          }
        } else if (frame.opcode === OPCODE.ping) {
          if (!socket.destroyed) socket.write(encodeFrame(OPCODE.pong, frame.payload));
        } else if (frame.opcode === OPCODE.close) {
          socket.end();
        }
      }
    });
    socket.on("close", () => clients.delete(client));
    socket.on("error", () => clients.delete(client));
  });

  await new Promise((resolve, reject) => {
    server.once("error", reject);
    server.listen(options.port === undefined ? 0 : options.port, "127.0.0.1", resolve);
  });
  const port = server.address().port;

  return {
    port,
    url: `ws://127.0.0.1:${port}`,
    stats,
    mode,
    documents: docs,
    // Close every client connection (the client sees an abnormal close), keep listening.
    dropClients() {
      for (const client of clients) {
        try { client.socket.destroy(); } catch (_) { /* already gone */ }
      }
      clients.clear();
    },
    async close() {
      this.dropClients();
      await new Promise((resolve) => server.close(() => resolve()));
    },
  };
}

// `node web/mock_lsp_server.mjs [PORT]`: a server to point a browser playground at.
const invokedDirectly = process.argv[1] &&
  import.meta.url === pathToFileURL(process.argv[1]).href;
if (invokedDirectly) {
  const port = Number(process.argv[2] || 8766);
  const mock = await startMockServer({ port });
  console.log(`mock lsp: ${mock.url} (open playground.html?lsp=${mock.url})`);
  process.on("SIGINT", async () => { await mock.close(); process.exit(0); });
}
