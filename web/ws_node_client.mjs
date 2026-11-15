// A minimal WebSocket client for the Node tests (`web/playground_lsp_test.mjs`), so the
// tests run on Node versions before the global `WebSocket` and without a dependency.
// It implements the part of the browser API that `web/lsp-client.js` uses: `onopen`,
// `onmessage`, `onclose`, `onerror`, `send`, `close` and `readyState`.
"use strict";
import net from "node:net";
import crypto from "node:crypto";
import { acceptKey, encodeFrame, FrameReader, OPCODE } from "./ws_frames.mjs";

export class NodeWebSocket {
  constructor(url) {
    this.url = String(url);
    this.readyState = 0;          // 0 connecting, 1 open, 2 closing, 3 closed
    this.onopen = null;
    this.onmessage = null;
    this.onclose = null;
    this.onerror = null;
    this.done = false;
    this.socket = null;
    this.reader = new FrameReader();
    this.handshake = Buffer.alloc(0);
    this.open = false;
    this.connect();
  }

  connect() {
    let url;
    try {
      url = new URL(this.url);
    } catch (e) {
      this.fail(new Error("invalid WebSocket URL: " + this.url));
      return;
    }
    if (url.protocol !== "ws:" && url.protocol !== "wss:") {
      this.fail(new Error("not a ws:// URL: " + this.url));
      return;
    }
    if (url.protocol === "wss:") {
      this.fail(new Error("the Node test client only speaks ws://"));
      return;
    }
    const port = Number(url.port || 80);
    const host = url.hostname.replace(/^\[|\]$/g, "");
    const path = (url.pathname || "/") + (url.search || "");
    const key = crypto.randomBytes(16).toString("base64");
    const expected = acceptKey(key);
    const socket = net.connect(port, host);
    this.socket = socket;
    socket.on("connect", () => {
      socket.write(
        `GET ${path} HTTP/1.1\r\n` +
        `Host: ${url.hostname}:${port}\r\n` +
        `Upgrade: websocket\r\n` +
        `Connection: Upgrade\r\n` +
        `Sec-WebSocket-Key: ${key}\r\n` +
        `Sec-WebSocket-Version: 13\r\n` +
        `Origin: http://127.0.0.1\r\n` +
        `\r\n`);
    });
    socket.on("data", (chunk) => this.onData(chunk, expected));
    socket.on("error", (e) => this.fail(e));
    socket.on("close", () => this.finish({ code: 1006, reason: "", wasClean: false }));
  }

  onData(chunk, expectedAccept) {
    if (!this.open) {
      this.handshake = Buffer.concat([this.handshake, chunk]);
      const end = this.handshake.indexOf("\r\n\r\n");
      if (end < 0) return;
      const head = this.handshake.subarray(0, end).toString("latin1");
      const rest = this.handshake.subarray(end + 4);
      const status = /^HTTP\/1\.[01] (\d{3})/.exec(head);
      const accept = /^sec-websocket-accept:\s*(\S+)/im.exec(head);
      if (!status || status[1] !== "101" || !accept || accept[1] !== expectedAccept) {
        this.fail(new Error("the server refused the WebSocket handshake"));
        return;
      }
      this.open = true;
      this.readyState = 1;
      if (typeof this.onopen === "function") this.onopen({ type: "open" });
      if (rest.length) this.onFrames(this.reader.push(rest));
      return;
    }
    this.onFrames(this.reader.push(chunk));
  }

  onFrames(frames) {
    for (const frame of frames) {
      if (frame.opcode === OPCODE.text || frame.opcode === OPCODE.binary) {
        if (typeof this.onmessage === "function") {
          this.onmessage({ data: frame.payload.toString("utf8") });
        }
      } else if (frame.opcode === OPCODE.ping) {
        if (this.socket && !this.socket.destroyed) {
          this.socket.write(encodeFrame(OPCODE.pong, frame.payload, { mask: true }));
        }
      } else if (frame.opcode === OPCODE.close) {
        let code = 1005;
        let reason = "";
        if (frame.payload.length >= 2) {
          code = frame.payload.readUInt16BE(0);
          reason = frame.payload.subarray(2).toString("utf8");
        }
        this.sendClose(code, "");
        this.finish({ code, reason, wasClean: true });
      }
    }
  }

  send(data) {
    if (this.readyState !== 1 || !this.socket || this.socket.destroyed) {
      throw new Error("the WebSocket is not open");
    }
    this.socket.write(encodeFrame(OPCODE.text, Buffer.from(String(data), "utf8"), { mask: true }));
  }

  close(code = 1000, reason = "") {
    if (this.done) return;
    this.readyState = 2;
    this.sendClose(code, reason);
    if (this.socket) this.socket.end();
    this.finish({ code, reason, wasClean: true });
  }

  sendClose(code, reason) {
    if (!this.socket || this.socket.destroyed) return;
    const payload = Buffer.alloc(2 + Buffer.byteLength(reason || ""));
    payload.writeUInt16BE(code, 0);
    payload.write(reason || "", 2);
    try { this.socket.write(encodeFrame(OPCODE.close, payload, { mask: true })); } catch (_) { /* closing */ }
  }

  fail(error) {
    if (this.done) return;
    if (typeof this.onerror === "function") this.onerror({ type: "error", message: error.message || String(error), error });
    if (this.socket) this.socket.destroy();
    this.finish({ code: 1006, reason: error.message || String(error), wasClean: false });
  }

  finish(event) {
    if (this.done) return;
    this.done = true;
    this.readyState = 3;
    if (this.socket) this.socket.destroy();
    if (typeof this.onclose === "function") this.onclose(event);
  }
}

// The `WebSocketImpl` to hand `LspClient` in a test.
export function connectWebSocket(url) {
  return new NodeWebSocket(url);
}
