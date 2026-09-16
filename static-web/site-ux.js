/**
 * Site UX: copy-friendly blueprint permalinks.
 * Anchors and drill-down TOC are injected at build time by enhance-site-ux.py.
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
    // Keep path as-is; replace hash with the stable node label.
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
    // Update location hash without jumping if already near the target.
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
        // Fallback: still navigate via the link semantics.
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
})();
