// Tests of the minimal widget client (web/widgets.mjs) under Node, with no browser: the
// sanitiser removes scripts, styles, event handlers and active URL schemes; a widget is
// rendered as an escaped title, a sandboxed iframe and escaped goals; two widgets keep
// their emission order. `sh web/test.sh` runs this beside the Wasm infoview tests.
//   usage: node web/widgets_test.mjs
import { sanitizeWidgetHtml, widgetHtml, renderWidgets, sampleWidgets } from "./widgets.mjs";

const failures = [];
const check = (name, ok) => { if (!ok) failures.push(name); };

const hostile = "<script>window.pwned = 1</script><style>body { display: none }</style>" +
  "<b onclick=\"window.pwned = 2\">ok</b><a href=\"javascript:window.pwned = 3\">no</a>" +
  "<img src=x onerror=\"window.pwned = 4\"><iframe src=\"data:text/html,<script>x</script>\"></iframe>";

const clean = sanitizeWidgetHtml(hostile);
check("no script element", !/<script/i.test(clean));
check("no style element", !/<style/i.test(clean));
check("no event handler", !/\son\w+\s*=/i.test(clean));
check("no javascript: URL", !/javascript\s*:/i.test(clean));
check("no data:text/html URL", !/data\s*:\s*text\/html/i.test(clean));
check("keeps the safe text", clean.includes(">ok<"));

const one = widgetHtml({ title: "<b>T</b>", html: hostile, goals: ["a<b"] });
check("title is escaped", one.includes("&lt;b&gt;T&lt;/b&gt;") && !one.includes("<b>T</b>"));
check("body is sandboxed", one.includes("sandbox") && one.includes("srcdoc="));
check("body has a content security policy", one.includes("Content-Security-Policy"));
check("body has no script", !/<script/i.test(one));
check("body has no style element", !/<style/i.test(one));
check("body has no event handler", !/\son\w+\s*=/i.test(one));
check("body has no javascript: URL", !/javascript\s*:/i.test(one));
check("body has no data:text/html URL", !/data\s*:\s*text\/html/i.test(one));
check("goals are escaped", one.includes("<pre class=\"widget-goal\">a&lt;b</pre>"));

const two = widgetHtml({ title: "First", html: "<b>one</b>", goals: [] }) +
  widgetHtml({ title: "Second", html: "<i>two</i>", goals: [] });
check("two widgets keep emission order", two.indexOf("First") < two.indexOf("Second"));

const root = { innerHTML: "" };
renderWidgets(root, sampleWidgets);
check("renderWidgets renders every widget", (root.innerHTML.match(/class="widget"/g) || []).length === 2);
check("renderWidgets keeps order", root.innerHTML.indexOf("Panel") < root.innerHTML.indexOf("Danger"));
check("renderWidgets output is safe", !/<script/i.test(root.innerHTML) &&
  !/\son\w+\s*=/i.test(root.innerHTML) && !/javascript\s*:/i.test(root.innerHTML));

if (failures.length) {
  console.error("widgets: FAILED: " + failures.join("; "));
  process.exit(1);
}
console.log("widgets: all checks passed");
