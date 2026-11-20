// The standalone infoview page's half under Node (web/infoview.js): the URL rule that
// picks the server, and the text its status line shows. The pane it mounts is
// web/playground-lsp.js, tested by web/playground_lsp_test.mjs; the page itself in a
// browser is web/chrome_test.mjs. No Wasm, no browser, no server.
//
//   node web/infoview_page_test.mjs
"use strict";
import { endpointOf } from "./infoview.js";

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
// (#430) the server's token rides along to the WebSocket, and the label leaves it out.
check("?port= with a token: the socket URL carries it",
  new URL(endpointOf("?port=1234&token=t0k").url).searchParams.get("token"), "t0k");
check("?port= with a token: the label hides it", endpointOf("?port=1234&token=t0k").label,
  "ws://127.0.0.1:1234/");
check("?lsp= with a token: the socket URL carries it",
  new URL(endpointOf("?lsp=ws://h:2&token=t0k").url).searchParams.get("token"), "t0k");
check("a token already in the ?lsp= URL is kept",
  new URL(endpointOf("?lsp=ws://h:2?token=in-url").url).searchParams.get("token"), "in-url");

// The status line moved to the runtime (`Goals.statusText`); the Wiz fixture
// `web/goals_gen.wiz` pins it with the goals markup.

if (failed) {
  console.log(`infoview page: ${failed} check(s) failed`);
  process.exit(1);
}
console.log("infoview page: all checks passed");
