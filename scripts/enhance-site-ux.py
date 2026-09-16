#!/usr/bin/env python3
"""Post-process Verso Blueprint html-multi output for site UX.

Adds:
  1) Stable human-friendly anchors (#node_label) + copy permalink controls
  2) Drill-down left TOC: chapter → group → statements

Designed to run AFTER `lake exe vbp build` on `_out/site/html-multi`.
Does not fork Verso; pure HTML/CSS/JS enhancement.
"""

from __future__ import annotations

import argparse
import html
import json
import re
import shutil
import sys
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent
STATIC_WEB = REPO_ROOT / "static-web"

WRAPPER_OPEN_RE = re.compile(
    r'<div class="bp_wrapper(?P<classes>[^"]*)"(?P<attrs>[^>]*)>',
    re.MULTILINE,
)
TITLE_RE = re.compile(r'\btitle="([^"]*)"')
ID_RE = re.compile(r'\bid="([^"]*)"')
TOC_NAV_RE = re.compile(r'<nav id="toc">.*?</nav>', re.DOTALL)
HEAD_LINK_RE = re.compile(
    r'(<link rel="stylesheet" href="verso-vars\.css">)',
    re.IGNORECASE,
)
TOC_RESIZE_SCRIPT_RE = re.compile(
    r'(<script src="toc-resize\.js"[^>]*></script>)',
    re.IGNORECASE,
)

# Chapter dir (first path segment of entry.href) → display handled via TOC rows.
ASSET_CSS = "site-ux.css"
ASSET_JS = "site-ux.js"


def load_manifest(site_root: Path) -> dict[str, Any]:
    path = site_root / "-verso-data" / "blueprint-manifest.json"
    if not path.is_file():
        raise SystemExit(f"missing blueprint manifest: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def chapter_dir_from_href(href: str) -> str:
    """Return first path segment of a manifest entry href (chapter folder)."""
    path = href.split("#", 1)[0].strip("/")
    if not path:
        return ""
    return path.split("/", 1)[0]


def short_group_title(group: dict[str, Any]) -> str:
    """Human-friendly short label for a blueprint group."""
    label = str(group.get("label") or "").strip()
    raw = str(group.get("title") or "").strip()
    # Prefer a short clause from the prose title when present.
    if raw:
        clause = re.split(r"[.;:]", raw, maxsplit=1)[0].strip()
        if 8 <= len(clause) <= 56:
            return clause
        if clause:
            return (clause[:53].rstrip() + "…") if len(clause) > 53 else clause
    if label:
        name = re.sub(r"_core$", "", label)
        name = name.replace("_", " ").strip()
        return name[:1].upper() + name[1:] if name else "Statements"
    return "Statements"


def friendly_href(entry_href: str, label: str) -> str:
    """Rewrite ugly --informal-preview-… hashes to #{label}."""
    path = entry_href.split("#", 1)[0]
    return f"{path}#{label}"


def index_groups_by_chapter(manifest: dict[str, Any]) -> dict[str, list[dict[str, Any]]]:
    by_chapter: dict[str, list[dict[str, Any]]] = {}
    for group in manifest.get("groups") or []:
        entries = group.get("entries") or []
        if not entries:
            continue
        # Most groups live under one chapter; bucket by majority href prefix.
        dirs = [chapter_dir_from_href(e.get("href") or "") for e in entries]
        dirs = [d for d in dirs if d]
        if not dirs:
            continue
        chapter = max(set(dirs), key=dirs.count)
        by_chapter.setdefault(chapter, []).append(group)
    return by_chapter


def detect_current_chapter(toc_html: str) -> str | None:
    """Infer current chapter directory from the TOC's .current row link."""
    m = re.search(
        r'<tr class="[^"]*\bcurrent\b[^"]*"[^>]*>.*?<a href="([^"#]+)',
        toc_html,
        re.DOTALL,
    )
    if m:
        return chapter_dir_from_href(m.group(1))
    m = re.search(
        r'<span class="current"><a href="([^"#]+)',
        toc_html,
    )
    if m:
        return chapter_dir_from_href(m.group(1))
    return None


def parse_book_toc_rows(toc_html: str) -> list[dict[str, str]]:
    """Parse chapter rows from the book split-toc table."""
    book = re.search(
        r'<div class="split-toc book">.*?<table>(.*?)</table>',
        toc_html,
        re.DOTALL,
    )
    if not book:
        return []
    rows = []
    for tr in re.finditer(r"<tr\b([^>]*)>(.*?)</tr>", book.group(1), re.DOTALL):
        attrs, inner = tr.group(1), tr.group(2)
        classes = re.search(r'class="([^"]*)"', attrs)
        cls = classes.group(1) if classes else ""
        num_m = re.search(r'<td class="num">([^<]*)</td>', inner)
        # Some unnumbered rows have a broken <td class="num"><td> … pattern.
        link_m = re.search(r'<a href="([^"]*)">([^<]*)</a>', inner)
        if not link_m:
            continue
        rows.append(
            {
                "classes": cls,
                "num": (num_m.group(1) if num_m else "").strip(),
                "href": link_m.group(1),
                "title": html.unescape(link_m.group(2).strip()),
                "chapter": chapter_dir_from_href(link_m.group(1)),
            }
        )
    return rows


def render_entries_ol(entries: list[dict[str, Any]], _id_prefix: str) -> str:
    items = []
    for i, entry in enumerate(entries):
        label = str(entry.get("label") or "").strip()
        title = str(entry.get("title") or label).strip()
        href = friendly_href(str(entry.get("href") or ""), label) if label else str(entry.get("href") or "")
        items.append(
            f'<li class="site-ux-toc-entry">'
            f'<a href="{html.escape(href, quote=True)}">{html.escape(title)}</a>'
            f"</li>"
        )
    return f'<ol class="site-ux-toc-nested site-ux-toc-entries">{"".join(items)}</ol>'


def render_groups_ol(
    groups: list[dict[str, Any]],
    *,
    id_prefix: str,
    expand_groups: bool,
) -> str:
    parts = ['<ol class="site-ux-toc-nested site-ux-toc-groups">']
    for gi, group in enumerate(groups):
        gid = f"{id_prefix}-g{gi}"
        gtitle = short_group_title(group)
        checked = " checked=\"checked\"" if expand_groups else ""
        entries = group.get("entries") or []
        parts.append('<li class="site-ux-toc-group">')
        parts.append('<div class="site-ux-toc-row">')
        parts.append(
            f'<label for="{html.escape(gid, quote=True)}" class="toggle-split-toc">'
            f'<input type="checkbox" class="toggle-split-toc" id="{html.escape(gid, quote=True)}"{checked}>'
            f"</label>"
        )
        parts.append(
            f'<span class="site-ux-toc-group-title">{html.escape(gtitle)}</span>'
        )
        parts.append("</div>")
        parts.append(render_entries_ol(entries, gid))
        parts.append("</li>")
    parts.append("</ol>")
    return "".join(parts)


def render_drilldown_toc(
    rows: list[dict[str, str]],
    by_chapter: dict[str, list[dict[str, Any]]],
    current_chapter: str | None,
) -> str:
    parts = ['<ol class="site-ux-toc site-ux-toc-book">']
    for i, row in enumerate(rows):
        chapter = row["chapter"]
        is_current = bool(current_chapter and chapter == current_chapter) or (
            "current" in row["classes"].split()
        )
        groups = by_chapter.get(chapter) or []
        has_kids = bool(groups)
        cid = f"site-ux-toc-ch-{i}-{chapter or 'x'}"
        li_cls = "site-ux-toc-chapter"
        if is_current:
            li_cls += " current"
        if "unnumbered" in row["classes"].split():
            li_cls += " unnumbered"
        parts.append(f'<li class="{li_cls}">')
        parts.append('<div class="site-ux-toc-row">')
        if has_kids:
            checked = " checked=\"checked\"" if is_current else ""
            parts.append(
                f'<label for="{html.escape(cid, quote=True)}" class="toggle-split-toc">'
                f'<input type="checkbox" class="toggle-split-toc" id="{html.escape(cid, quote=True)}"{checked}>'
                f"</label>"
            )
        else:
            parts.append('<span class="no-toggle"></span>')
        if row["num"]:
            parts.append(f'<span class="num">{html.escape(row["num"])}</span>')
        parts.append(
            f'<a href="{html.escape(row["href"], quote=True)}">{html.escape(row["title"])}</a>'
        )
        parts.append("</div>")
        if has_kids:
            parts.append(
                render_groups_ol(
                    groups,
                    id_prefix=cid,
                    expand_groups=is_current,
                )
            )
        parts.append("</li>")
    parts.append("</ol>")
    return "".join(parts)


def render_local_toc(
    groups: list[dict[str, Any]],
    *,
    chapter_title: str,
    chapter_href: str,
    chapter_num: str,
) -> str:
    """Fill the second (page-local) split-toc pane."""
    checked_root = ' checked="checked"'
    parts = [
        '<div class="split-toc site-ux-local-toc">',
        '<div class="title">',
        f'<label for="site-ux-local-root" class="toggle-split-toc">'
        f'<input type="checkbox" class="toggle-split-toc" id="site-ux-local-root"{checked_root}>'
        f"</label>",
    ]
    if chapter_num:
        parts.append(f'<span class="number">{html.escape(chapter_num)}</span> ')
    parts.append(
        f'<span class="current"><a href="{html.escape(chapter_href, quote=True)}">'
        f"{html.escape(chapter_title)}</a></span>"
    )
    parts.append("</div>")
    # Local outline: groups → statements (groups expanded).
    parts.append(
        render_groups_ol(groups, id_prefix="site-ux-local", expand_groups=True).replace(
            'class="site-ux-toc-nested site-ux-toc-groups"',
            'class="site-ux-toc site-ux-toc-nested site-ux-toc-groups"',
            1,
        )
    )
    parts.append("</div>")
    return "".join(parts)


def enhance_toc(toc_html: str, by_chapter: dict[str, list[dict[str, Any]]]) -> str:
    rows = parse_book_toc_rows(toc_html)
    if not rows:
        return toc_html
    current = detect_current_chapter(toc_html)
    drilldown = render_drilldown_toc(rows, by_chapter, current)

    # Replace the book table with the drill-down list; keep the title row.
    def repl_book(m: re.Match[str]) -> str:
        return (
            f'{m.group(1)}{drilldown}</div>'
        )

    new_toc, n = re.subn(
        r'(<div class="split-toc book">\s*'
        r'<div class="title">.*?</div>\s*)'
        r'<table>.*?</table>\s*</div>',
        repl_book,
        toc_html,
        count=1,
        flags=re.DOTALL,
    )
    if n != 1:
        return toc_html

    # Enhance / replace the secondary split-toc when we know the current chapter.
    if current and current in by_chapter:
        row = next((r for r in rows if r["chapter"] == current), None)
        local = render_local_toc(
            by_chapter[current],
            chapter_title=(row["title"] if row else current),
            chapter_href=(row["href"] if row else f"{current}/"),
            chapter_num=(row["num"] if row else ""),
        )
        new_toc2, n2 = re.subn(
            r'<div class="split-toc">\s*'
            r'<div class="title">.*?</div>\s*'
            r'</div>',
            local,
            new_toc,
            count=1,
            flags=re.DOTALL,
        )
        if n2 == 1:
            new_toc = new_toc2
    return new_toc


def facet_from_legacy_id(legacy_id: str, title: str) -> str | None:
    """Return stable anchor id for a wrapper, or None to skip."""
    if not title or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", title):
        return None
    if legacy_id == f"--informal-preview-{title}--statement":
        return title
    if legacy_id == f"--informal-preview-{title}--proof":
        return f"{title}--proof"
    # Fallback: statement-like wrappers with a clean title but odd id.
    if "--statement" in legacy_id and "bp_code_panel" not in legacy_id:
        return title
    return None


def enhance_wrappers(page_html: str) -> tuple[str, int]:
    """Insert stable anchors + permalink widgets into statement/proof wrappers."""
    count = 0
    out: list[str] = []
    pos = 0
    for m in WRAPPER_OPEN_RE.finditer(page_html):
        out.append(page_html[pos : m.start()])
        full = m.group(0)
        classes = m.group("classes")
        attrs = m.group("attrs")
        pos = m.end()

        if "bp_code_panel" in classes:
            out.append(full)
            continue

        title_m = TITLE_RE.search(attrs)
        id_m = ID_RE.search(attrs)
        if not title_m or not id_m:
            out.append(full)
            continue

        title = title_m.group(1)
        legacy_id = id_m.group(1)
        anchor = facet_from_legacy_id(legacy_id, title)
        if not anchor:
            out.append(full)
            continue

        # Skip if we already enhanced this wrapper.
        lookahead = page_html[m.end() : m.end() + 120]
        if 'class="bp-stable-anchor"' in lookahead or f'id="{anchor}"' in lookahead[:80]:
            out.append(full)
            continue

        anchor_el = (
            f'<span id="{html.escape(anchor, quote=True)}" class="bp-stable-anchor" '
            f'data-bp-node="{html.escape(title, quote=True)}"></span>'
        )
        permalink = (
            f'<span class="permalink-widget inline bp-node-permalink" '
            f'data-anchor="{html.escape(anchor, quote=True)}">'
            f'<a href="#{html.escape(anchor, quote=True)}" title="Copy permalink" '
            f'aria-label="Copy permalink to {html.escape(anchor, quote=True)}">🔗</a>'
            f"</span>"
        )

        # Emit opening tag + stable anchor immediately inside the wrapper.
        out.append(full)
        out.append(anchor_el)

        # Insert permalink into the heading title row when present shortly after.
        # Search a bounded window for the title row close.
        window_end = min(len(page_html), pos + 2500)
        window = page_html[pos:window_end]
        row_close = re.search(
            r'(<div class="bp_heading_title_row[^"]*">.*?)(</div>)',
            window,
            re.DOTALL,
        )
        if row_close and "bp-node-permalink" not in row_close.group(1):
            insert_at = pos + row_close.start(2)
            out.append(page_html[pos:insert_at])
            out.append(permalink)
            pos = insert_at
            count += 1
        else:
            # Fallback: place permalink right after the anchor.
            out.append(permalink)
            count += 1

    out.append(page_html[pos:])
    return "".join(out), count


def inject_assets(page_html: str) -> str:
    if ASSET_CSS not in page_html:
        page_html, n = HEAD_LINK_RE.subn(
            rf'\1\n    <link rel="stylesheet" href="{ASSET_CSS}">',
            page_html,
            count=1,
        )
        if n == 0:
            # Fallback: before </head>
            page_html = page_html.replace(
                "</head>",
                f'    <link rel="stylesheet" href="{ASSET_CSS}">\n  </head>',
                1,
            )
    if ASSET_JS not in page_html:
        page_html, n = TOC_RESIZE_SCRIPT_RE.subn(
            rf'\1\n    <script src="{ASSET_JS}" defer="defer"></script>',
            page_html,
            count=1,
        )
        if n == 0:
            page_html = page_html.replace(
                "</body>",
                f'    <script src="{ASSET_JS}" defer="defer"></script>\n  </body>',
                1,
            )
    return page_html


def copy_static_assets(site_root: Path) -> None:
    for name in (ASSET_CSS, ASSET_JS):
        src = STATIC_WEB / name
        if not src.is_file():
            raise SystemExit(f"missing static asset: {src}")
        shutil.copy2(src, site_root / name)


def enhance_page(path: Path, by_chapter: dict[str, list[dict[str, Any]]]) -> dict[str, int]:
    original = path.read_text(encoding="utf-8")
    page = original
    stats = {"permalinks": 0, "toc": 0}

    page, n = enhance_wrappers(page)
    stats["permalinks"] = n

    def toc_sub(m: re.Match[str]) -> str:
        enhanced = enhance_toc(m.group(0), by_chapter)
        if enhanced != m.group(0):
            stats["toc"] = 1
        return enhanced

    page, _ = TOC_NAV_RE.subn(toc_sub, page, count=1)
    page = inject_assets(page)

    if page != original:
        path.write_text(page, encoding="utf-8")
    return stats


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--site-root",
        type=Path,
        default=None,
        help="Path to html-multi site root (default: <repo>/_out/site/html-multi)",
    )
    args = parser.parse_args(argv)
    site_root = (args.site_root or (REPO_ROOT / "_out" / "site" / "html-multi")).resolve()
    if not site_root.is_dir():
        raise SystemExit(f"site root not found: {site_root}")

    manifest = load_manifest(site_root)
    by_chapter = index_groups_by_chapter(manifest)
    copy_static_assets(site_root)

    html_files = sorted(site_root.rglob("*.html"))
    total_permalinks = 0
    toc_pages = 0
    for path in html_files:
        # Skip search/find utility pages that are not chapter content if desired;
        # still safe to enhance (TOC + assets).
        stats = enhance_page(path, by_chapter)
        total_permalinks += stats["permalinks"]
        toc_pages += stats["toc"]

    print(
        f"enhance-site-ux: {len(html_files)} HTML files; "
        f"{total_permalinks} permalinks; "
        f"{toc_pages} TOCs updated; "
        f"{len(by_chapter)} chapters with groups"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
