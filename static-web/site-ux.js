/**
 * Site UX: permalinks, collapsed Lean panels, TOC active highlight, dev drawer.
 * Anchors and drill-down TOC are injected at build time by enhance-site-ux.py.
 * Theme default (modern) is set by an early head script from the enhancer.
 */
(function () {
  function flashCopied(widget) {
    widget.classList.add("is-copied");
    let note = widget.querySelector(".bp-permalink-copied");
    if (!note) {
      note = document.createElement("span");
      note.className = "bp-permalink-copied";
      note.setAttribute("aria-live", "polite");
      widget.appendChild(note);
    }
    note.textContent = "Copied";
    window.clearTimeout(widget._bpCopiedTimer);
    widget._bpCopiedTimer = window.setTimeout(function () {
      note.textContent = "";
      widget.classList.remove("is-copied");
    }, 1400);
  }

  function permalinkUrl(anchorId) {
    const url = new URL(window.location.href);
    url.hash = anchorId;
    return url.toString();
  }

  async function copyText(text) {
    if (navigator.clipboard && navigator.clipboard.writeText) {
      await navigator.clipboard.writeText(text);
      return;
    }
    const ta = document.createElement("textarea");
    ta.value = text;
    ta.setAttribute("readonly", "");
    ta.style.position = "fixed";
    ta.style.left = "-9999px";
    document.body.appendChild(ta);
    ta.select();
    document.execCommand("copy");
    document.body.removeChild(ta);
  }

  function onPermalinkActivate(event) {
    const widget = event.target.closest(".bp-node-permalink");
    if (!widget) return;
    const anchorId = widget.getAttribute("data-anchor");
    if (!anchorId) return;
    event.preventDefault();
    const href = permalinkUrl(anchorId);
    if (widget.getAttribute("data-update-hash") !== "false") {
      try {
        history.replaceState(null, "", "#" + anchorId);
      } catch (_) {
        /* ignore */
      }
    }
    copyText(href)
      .then(function () {
        flashCopied(widget);
      })
      .catch(function () {
        window.location.hash = anchorId;
      });
  }

  document.addEventListener("click", function (event) {
    if (event.target.closest(".bp-node-permalink")) {
      onPermalinkActivate(event);
    }
  });

  document.addEventListener("keydown", function (event) {
    if (event.key !== "Enter" && event.key !== " ") return;
    if (!event.target.closest(".bp-node-permalink")) return;
    onPermalinkActivate(event);
  });

  /** Collapse Lean/code panels so math statement stays primary. */
  function collapseCodePanels() {
    document
      .querySelectorAll("details.bp_code_block.bp_code_panel, details.bp_code_panel")
      .forEach(function (el) {
        el.removeAttribute("open");
      });
  }

  /**
   * Move build metadata + style switcher into a corner "Site / dev" drawer
   * so they leave the primary reading surface.
   */
  function installDevDrawer() {
    if (document.getElementById("site-ux-dev-drawer")) return;
    if (!document.body) return;

    const drawer = document.createElement("details");
    drawer.id = "site-ux-dev-drawer";
    const summary = document.createElement("summary");
    summary.textContent = "Site / about";
    summary.title = "Build metadata and appearance (dev)";
    const body = document.createElement("div");
    body.className = "site-ux-dev-body";

    const meta = document.querySelector(".bp_build_metadata");
    if (meta && meta.parentElement) {
      body.appendChild(meta);
    }

    // Style switcher is created by Verso blueprint JS; observe until present.
    function adoptSwitcher() {
      const sw = document.getElementById("bp-style-switcher");
      if (sw && sw.parentElement !== body) {
        body.appendChild(sw);
        return true;
      }
      return false;
    }

    drawer.appendChild(summary);
    drawer.appendChild(body);
    document.body.appendChild(drawer);

    if (!adoptSwitcher()) {
      let tries = 0;
      const timer = window.setInterval(function () {
        tries += 1;
        if (adoptSwitcher() || tries > 40) window.clearInterval(timer);
      }, 100);
    }
  }

  /** Highlight the TOC entry for the statement nearest the viewport top. */
  function installTocActiveHighlight() {
    const toc = document.querySelector("#toc .site-ux-toc");
    if (!toc) return;

    const entries = Array.from(toc.querySelectorAll(".site-ux-toc-entry a[href*='#']"));
    if (!entries.length) return;

    const byId = new Map();
    entries.forEach(function (a) {
      const href = a.getAttribute("href") || "";
      const hash = href.includes("#") ? href.slice(href.indexOf("#") + 1) : "";
      if (!hash) return;
      try {
        const id = decodeURIComponent(hash);
        if (!byId.has(id)) byId.set(id, []);
        byId.get(id).push(a);
      } catch (_) {
        /* ignore */
      }
    });

    let currentId = null;

    function setActive(id) {
      if (id === currentId) return;
      currentId = id;
      toc.querySelectorAll(".site-ux-toc-entry.is-active").forEach(function (li) {
        li.classList.remove("is-active");
      });
      toc.querySelectorAll(".site-ux-toc-entry a.is-active").forEach(function (a) {
        a.classList.remove("is-active");
      });
      if (!id || !byId.has(id)) return;
      byId.get(id).forEach(function (a) {
        a.classList.add("is-active");
        const li = a.closest(".site-ux-toc-entry");
        if (li) li.classList.add("is-active");
      });
    }

    const anchors = [];
    byId.forEach(function (_links, id) {
      const el = document.getElementById(id);
      if (el) anchors.push(el);
    });
    if (!anchors.length || !("IntersectionObserver" in window)) {
      // Fallback: hash
      if (location.hash.length > 1) setActive(decodeURIComponent(location.hash.slice(1)));
      return;
    }

    const headerOffset = 72;
    const observer = new IntersectionObserver(
      function (records) {
        // Pick the intersecting entry closest to the top of the reading pane.
        let best = null;
        let bestTop = Infinity;
        records.forEach(function (rec) {
          if (!rec.isIntersecting) return;
          const top = rec.boundingClientRect.top;
          if (top >= headerOffset - 40 && top < bestTop) {
            bestTop = top;
            best = rec.target.id;
          }
        });
        if (best) setActive(best);
      },
      {
        root: null,
        rootMargin: "-64px 0px -55% 0px",
        threshold: [0, 0.1, 0.25, 0.5, 1],
      }
    );

    anchors.forEach(function (el) {
      observer.observe(el);
    });

    if (location.hash.length > 1) {
      try {
        setActive(decodeURIComponent(location.hash.slice(1)));
      } catch (_) {
        /* ignore */
      }
    }
  }

  function boot() {
    collapseCodePanels();
    installDevDrawer();
    installTocActiveHighlight();
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", boot);
  } else {
    boot();
  }
})();
