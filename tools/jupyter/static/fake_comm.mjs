// A fake Jupyter comm and kernel for the widget front end test.
//
// The envelope is the one `tools/jupyter/wiz_kernel/wire.py` signs and the kernel
// tests read: a message has `header` (msg_type, msg_id, version 5.3, ...), `content`,
// `parent_header`, `metadata` and `buffers`.  A comm message's content is
// `{comm_id, target_name?, data}`.  There is no ZeroMQ here: `FakeComm.deliver` calls
// the front end's `on_msg` handler directly, which is exactly what a client that
// received the iopub frame would do.
//
// The "kernel" is a small state machine over a fixture: it opens the comm with the
// initial SSR HTML, receives `{event, index, value}` from the front end and answers
// with `comm_msg` carrying `{method: "update", patch}`.  The fixture supplies the patch
// list (the output of `React.patchesJson`), so the test pins the wire shape and the
// DOM patch, not a re-implementation of the Wiz diff.
"use strict";

let nextId = 0;

export function message(msgType, content, { parent = {}, metadata = {} } = {}) {
  return {
    header: {
      msg_id: "fake-" + ++nextId,
      username: "kernel",
      session: "fake-session",
      date: "2026-11-15T00:00:00Z",
      msg_type: msgType,
      version: "5.3",
    },
    parent_header: parent,
    metadata,
    content,
    buffers: [],
  };
}

export class FakeComm {
  constructor({ comm_id = "widget-1", target_name = "wiz.widget" } = {}) {
    this.comm_id = comm_id;
    this.target_name = target_name;
    this.sent = [];          // front end -> kernel payloads
    this.received = [];      // kernel -> front end messages (comm_open, comm_msg, ...)
    this._onMsg = [];
    this.kernel = null;
  }

  on_msg(fn) {
    this._onMsg.push(fn);
    return this;
  }

  send(payload) {
    this.sent.push(payload);
    if (this.kernel) this.kernel.receive(this, payload);
  }

  // Deliver a kernel message to the front end, in Jupyter's envelope shape.
  deliver(msgType, content, options) {
    const msg = message(msgType, { comm_id: this.comm_id, ...content }, options);
    this.received.push(msg);
    for (const fn of this._onMsg) fn(msg);
    return msg;
  }

  open(data) {
    return this.deliver("comm_open", { target_name: this.target_name, data });
  }

  get messages() {
    return this.received.map((m) => m.header.msg_type);
  }
}

export class FakeKernel {
  constructor(fixture, comm) {
    this.fixture = fixture;
    this.comm = comm;
    this.received = [];   // front end -> kernel payloads, in order
    this.steps = [];      // the fixture step names the front end triggered
    comm.kernel = this;
  }

  start() {
    this.comm.open({ html: this.fixture.html, handlers: this.fixture.handlers });
    return this;
  }

  receive(comm, payload) {
    this.received.push(payload);
    const step = this.stepFor(payload);
    if (!step) {
      comm.deliver("comm_msg", { data: { method: "error", payload,
        error: "no fixture step for this event" } });
      return;
    }
    this.steps.push(step.name);
    comm.deliver("comm_msg", {
      data: { method: "update", step: step.name, patch: step.patch },
    });
  }

  // Match on event and handler index; when the fixture step names a `value`, the front
  // end must have forwarded that control's value too.
  stepFor(payload) {
    for (const [name, step] of Object.entries(this.fixture.steps)) {
      if (payload.event !== step.event) continue;
      if (Number(payload.index) !== Number(step.index)) continue;
      if (step.value !== undefined && String(payload.value) !== String(step.value)) continue;
      return { ...step, name };
    }
    return null;
  }
}
