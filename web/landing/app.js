// The landing page's mount of the quantity island (`web/landing_ui.wiz`).
//
// The page is already the whole component: `web/landing/static_gen.wiz` rendered it at
// build time and the element carries `data-wiz-ssr`. `mount` adopts that tree when the
// hash matches and attaches the select's `change` listener; every step is a patch the
// runtime computes (one `setAttr "class"` on the app's root), never a node this page
// makes. `data-live` tells the stylesheet the control is operable, so a failed mount
// leaves the static explainer (all three panels, no inert select) instead of a page
// that looks interactive and is not.
import { mount } from "./framework/mount.js";

const el = document.getElementById("quantity-app");
if (el) {
  try {
    await mount(el, {
      module: () => import("./wiz-landing-ui.mjs"),
      events: ["change"],
    });
    el.setAttribute("data-live", "");
  } catch (e) {
    // The static panels are the page; one warning is the whole failure path for a
    // progressive enhancement (mount has already left the tree and, for an island,
    // written its reason into `data-wiz-error`).
    console.warn("landing: the quantity explorer stayed static: " +
      (e && e.message ? e.message : e));
  }
}
