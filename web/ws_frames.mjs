// RFC 6455 frames for the tests' WebSocket pieces (Node only; `Buffer`, `node:crypto`).
// The browser page uses its own WebSocket, so this file never ships to the site.
//
//   encodeFrame(1, Buffer.from(text), {mask: true})   a client → server text frame
//   const reader = new FrameReader(); reader.push(chunk) → complete frames
//
// Fragmented messages are reassembled; ping, pong and close are passed through. The
// payload limit is the server's (`Wiz/WebSocket.lean` closes above 256 MiB).
"use strict";
import crypto from "node:crypto";

export const OPCODE = { continuation: 0x0, text: 0x1, binary: 0x2, close: 0x8, ping: 0x9, pong: 0xa };

const GUID = "258EAFA5-E914-47DA-95CA-C5AB0DC85B11";

// The `Sec-WebSocket-Accept` value for a client's key (RFC 6455 §4.2.2).
export function acceptKey(key) {
  return crypto.createHash("sha1").update(String(key) + GUID).digest("base64");
}

export function encodeFrame(opcode, payload, options = {}) {
  const body = Buffer.isBuffer(payload) ? payload : Buffer.from(String(payload), "utf8");
  const mask = options.mask === true;
  const length = body.length;
  let head;
  if (length < 126) {
    head = Buffer.alloc(2);
    head[1] = length;
  } else if (length < 65536) {
    head = Buffer.alloc(4);
    head[1] = 126;
    head.writeUInt16BE(length, 2);
  } else {
    head = Buffer.alloc(10);
    head[1] = 127;
    head.writeBigUInt64BE(BigInt(length), 2);
  }
  head[0] = 0x80 | (opcode & 0x0f);          // FIN, no RSV bits
  head[1] |= mask ? 0x80 : 0x00;
  if (!mask) return Buffer.concat([head, body]);
  const key = crypto.randomBytes(4);
  const masked = Buffer.alloc(length);
  for (let i = 0; i < length; i++) masked[i] = body[i] ^ key[i % 4];
  return Buffer.concat([head, key, masked]);
}

export class FrameReader {
  constructor(options = {}) {
    this.maxPayload = options.maxPayload || 256 * 1024 * 1024;
    this.buffer = Buffer.alloc(0);
    this.fragments = [];
    this.fragmentOpcode = null;
    this.fragmentLength = 0;
  }

  // Feed bytes; returns the messages/frames completed by them.
  push(chunk) {
    this.buffer = this.buffer.length === 0 ? Buffer.from(chunk) : Buffer.concat([this.buffer, chunk]);
    const frames = [];
    for (;;) {
      const frame = this.read();
      if (!frame) break;
      if (frame.opcode >= 0x8) { frames.push(frame); continue; }   // control frame
      if (frame.opcode === OPCODE.continuation) {
        if (this.fragmentOpcode === null) continue;                // stray continuation
        this.fragments.push(frame.payload);
        this.fragmentLength += frame.payload.length;
        if (frame.fin) {
          const payload = Buffer.concat(this.fragments);
          frames.push({ opcode: this.fragmentOpcode, payload, fin: true });
          this.fragments = [];
          this.fragmentOpcode = null;
          this.fragmentLength = 0;
        }
        continue;
      }
      if (frame.fin) {
        frames.push(frame);
      } else {
        this.fragments = [frame.payload];
        this.fragmentOpcode = frame.opcode;
        this.fragmentLength = frame.payload.length;
      }
    }
    return frames;
  }

  read() {
    const buffer = this.buffer;
    if (buffer.length < 2) return null;
    const fin = (buffer[0] & 0x80) !== 0;
    const opcode = buffer[0] & 0x0f;
    const masked = (buffer[1] & 0x80) !== 0;
    let length = buffer[1] & 0x7f;
    let offset = 2;
    if (length === 126) {
      if (buffer.length < 4) return null;
      length = buffer.readUInt16BE(2);
      offset = 4;
    } else if (length === 127) {
      if (buffer.length < 10) return null;
      const big = buffer.readBigUInt64BE(2);
      if (big > BigInt(this.maxPayload)) throw new Error("WebSocket frame too large");
      length = Number(big);
      offset = 10;
    }
    if (length > this.maxPayload) throw new Error("WebSocket frame too large");
    let mask = null;
    if (masked) {
      if (buffer.length < offset + 4) return null;
      mask = buffer.subarray(offset, offset + 4);
      offset += 4;
    }
    if (buffer.length < offset + length) return null;
    const payload = Buffer.from(buffer.subarray(offset, offset + length));
    if (mask) for (let i = 0; i < payload.length; i++) payload[i] ^= mask[i % 4];
    this.buffer = buffer.subarray(offset + length);
    return { opcode, payload, fin };
  }
}
