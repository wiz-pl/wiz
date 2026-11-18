// The standalone infoview page's half under Node (web/infoview.js): the URL rule that
// picks the server, and the text its status line shows. The pane it mounts is
// web/playground-lsp.js, tested by web/playground_lsp_test.mjs; the page itself in a
// browser is web/chrome_test.mjs. No Wasm, no browser, no server.
//
//   node web/infoview_page_test.mjs
"use strict";
import { endpointOf, statusText } from "./infoview.js";

let failed = 0;
function check(name, got, want) {
  if (Object.is(got, want)) console.log(`ok: ${name}`);
  else {
    failed++;
    console.log(`FAIL: ${name}\n  want: ${JSON.stringify(want)}\n  got:  ${JSON.stringify(got)}`);
  }
}

// `?port=` is the page's old parameter (and what `wiz lsp --ws` prints as a default).
check("no query: the default port", endpointOf("").url, "ws://127.0.0.1:8765");
check("?port=: a local server", endpointOf("?port=1234").url, "ws://127.0.0.1:1234");
check("?port=off: the pane's no-server spelling", endpointOf("?port=off"), null);
// `?lsp=` is the playground's spelling; it wins.
check("?lsp=: a ws URL", endpointOf("?lsp=ws://example:1").url, "ws://example:1");
check("?lsp= wins over ?port=", endpointOf("?port=1&lsp=ws://h:2").url, "ws://h:2");
check("?lsp=: a bare port", endpointOf("?lsp=9999").url, "ws://127.0.0.1:9999");
// `off` is the pane with no server, as in the playground.
check("?lsp=off: no server", endpointOf("?lsp=off"), null);
// (#430) `wiz lsp --ws` refuses a connection without its token: the page's `?token=`
// goes into the socket's URL (what `web/bridge.sh` prints), and the shown label leaves
// it out (it is a secret).
check("?token=: into the socket's URL", endpointOf("?port=1234&token=abc").url,
  "ws://127.0.0.1:1234/?token=abc");
check("?lsp= with ?token=", endpointOf("?lsp=ws://example:1&token=abc").url,
  "ws://example:1/?token=abc");
check("?token=: the label leaves it out", endpointOf("?port=1234&token=abc").label,
  "ws://127.0.0.1:1234/");

// The status line's vocabulary (the page's `#status`).
check("status: open", statusText({ state: "open" }, false), "connected");
check("status: connecting", statusText({ state: "connecting" }, false), "connecting");
check("status: following", statusText({ state: "connecting" }, true), "following the editor");
check("status: closed", statusText({ state: "closed" }, false), "disconnected (is `wiz lsp --ws` running?)");
check("status: failed", statusText({ state: "failed", endpoint: "ws://127.0.0.1:1" }, false),
  "cannot connect to ws://127.0.0.1:1");
check("status: no server", statusText({ state: "no-server" }, false), "no server");

if (failed) {
  console.log(`infoview page: ${failed} check(s) failed`);
  process.exit(1);
}
console.log("infoview page: all checks passed");
