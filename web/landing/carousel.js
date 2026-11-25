// The landing carousel's progressive enhancement: switch between the panels that are
// already on the page, and nothing else.
//
// With no JavaScript every panel is visible and the tabs are plain links to
// `#/s/<name>`; the browser scrolls to the panel and `:target` marks it. This script
// adds the switch: roving tabindex, arrow/Home/End, exactly one `aria-selected`, a
// polite announcement after a user action, and `history.replaceState` so a selection
// is still a deep link without one history entry per arrow key. It builds no DOM: the
// only mutations are attributes and focus, and copy is a host capability
// (`navigator.clipboard`) that simply does not appear when the browser cannot do it.
(() => {
  "use strict";
  const root = document.getElementById("carousel");
  if (!root || typeof root.querySelectorAll !== "function") return;
  const tabs = Array.from(root.querySelectorAll('[role="tab"]'));
  const panels = tabs.map((tab) => document.getElementById(tab.getAttribute("aria-controls")));
  if (tabs.length === 0 || panels.some((panel) => !panel)) return;
  const status = document.getElementById("carousel-status");
  const list = root.querySelector('[role="tablist"]');
  let index = 0;

  const labelOf = (tab) => (tab.textContent || "").trim();

  function select(next, { focus = false, replace = false, announce = true } = {}) {
    index = Math.max(0, Math.min(tabs.length - 1, next));
    tabs.forEach((tab, k) => {
      const on = k === index;
      tab.setAttribute("aria-selected", on ? "true" : "false");
      tab.setAttribute("tabindex", on ? "0" : "-1");
      panels[k].toggleAttribute("data-active", on);
    });
    if (focus) tabs[index].focus();
    if (replace) {
      try { history.replaceState(null, "", tabs[index].getAttribute("href")); } catch { /* file:// */ }
    }
    if (status && announce) {
      status.textContent = labelOf(tabs[index]) + ", " + (index + 1) + " of " + tabs.length;
    }
  }

  function fromHash() {
    let id = "";
    try { id = decodeURIComponent(location.hash.slice(1)); } catch { return 0; }
    const i = panels.findIndex((panel) => panel.id === id);
    return i < 0 ? 0 : i;
  }

  // Enhance after the first paint has parsed: the panels are the page until now.
  root.setAttribute("data-carousel", "on");
  select(fromHash(), { announce: false });

  if (list) {
    list.addEventListener("keydown", (e) => {
      const keys = ["ArrowRight", "ArrowDown", "ArrowLeft", "ArrowUp", "Home", "End"];
      if (!keys.includes(e.key)) return;
      e.preventDefault();
      let next = index;
      if (e.key === "ArrowRight" || e.key === "ArrowDown") next = (index + 1) % tabs.length;
      else if (e.key === "ArrowLeft" || e.key === "ArrowUp") next = (index - 1 + tabs.length) % tabs.length;
      else if (e.key === "Home") next = 0;
      else next = tabs.length - 1;
      select(next, { focus: true, replace: true });
    });
  }

  // A click already navigates to the tab's href; the hash then says which panel. Do not
  // move focus: the clicked link has it.
  addEventListener("hashchange", () => select(fromHash(), { announce: true }));

  // Copy is a browser capability, not page state: the buttons are `hidden` in the HTML
  // and only a browser with a clipboard API gets them.
  const clipboard = navigator.clipboard;
  if (clipboard && typeof clipboard.writeText === "function") {
    for (const button of root.querySelectorAll(".copy")) {
      const panel = document.getElementById(button.getAttribute("data-copy"));
      const code = panel && panel.querySelector("code");
      if (!code) continue;
      button.hidden = false;
      button.addEventListener("click", async () => {
        const text = code.textContent;
        try {
          await clipboard.writeText(text);
          button.textContent = "Copied";
          setTimeout(() => { button.textContent = "Copy"; }, 1500);
          if (status) status.textContent = "Copied " + labelOf(tabs[index]);
        } catch {
          // A refused clipboard (an insecure context, a denied permission) leaves the
          // code selectable; the button keeps its label.
        }
      });
    }
  }
})();
