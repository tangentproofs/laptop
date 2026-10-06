# aptop.tangentcode.com — deploy notes

Lean deploy package for [aptop.tangentcode.com](https://aptop.tangentcode.com):
home + Netty under `/netty/`, Interpreter link “coming soon” under `/interp/`.
This directory is the survey and the one path cornerbot / the Linode host should
follow. Do **not** build Mathlib-heavy LaPToP/interp on the aptop box for v1.

Repo is **public**: `https://github.com/tangentproofs/laptop` (clone as
`michal` / `tangentstorm` via HTTPS or SSH). Checkout on the host:

```
/home/michal/ver/laptop
```

Host: tangentcode Linode `45.79.174.182` (box ~4 GB RAM, disk tight).

## Public layout

| Path | What |
|------|------|
| `/` | Static home (`deploy/aptop/site/`) |
| `/netty/` | Netty three-pane UI (Node + Lean kernel) |
| `/interp/` | Editable CodeMirror runner + Symbols sheet (loopback `:4712` may be stubbed) |
| `/examples/` | Highlighted editable demos + Symbols sheet |
| `/netty/` book examples | `.calc` files under `netty-web/public/examples/` load into the proof pane |
| `/docs/` | Optional later |

## Upstreams (loopback only)

| Service | Bind | Notes |
|---------|------|-------|
| Netty Node | `127.0.0.1:4711` | Serves `netty-web/public/` + `POST /api` |
| Interp (later) | `127.0.0.1:4712` | Web wrapper **not ready** — do not install a broken unit |

## Architecture survey

### Netty — not pure static

1. Browser loads `public/index.html` (relative CSS/JS: `./netty.css`, `./js/client.js`).
2. Client `POST`s JSON to **`api` relative to the page URL** (see below).
3. Node (`netty-web/dist/server.js`) serves static files and forwards `/api` to a
   long-lived Lean kernel over stdin/stdout.
4. Kernel: `lake exe netty --serve` or, after build,
   `.lake/build/bin/netty --serve`. **Netty has no Mathlib dependency.**

### Interpreter — CLI only for v1

- CLI today: `lake exe interp` (needs LaPToP + Mathlib oleans).
- Web runner / wrapper is **not ready**. Home links to `/interp/` as “coming
  soon”; that page shows the CodeMirror mode with a read-only sample.
- Do **not** build interp on this box for v1 unless necessary (RAM/disk).

## Critical: Netty under `/netty/`

The client used to `fetch('/api', …)`, which breaks when the UI is served at
`https://aptop.tangentcode.com/netty/` (would hit site root `/api`).

It now resolves the API path from the page URL:

```ts
function apiUrl(): string {
  const base = window.location.pathname.endsWith('/')
    ? window.location.pathname
    : window.location.pathname.replace(/\/[^/]*$/, '/');
  return new URL('api', window.location.origin + base).pathname;
}
```

So at `/netty/` (or `/netty/index.html`) the browser POSTs to **`/netty/api`**.

Nginx must **strip the `/netty/` prefix** when proxying so the Node server still
sees `/` and `/api`:

```nginx
location /netty/ {
  proxy_pass http://127.0.0.1:4711/;  # trailing slash strips /netty/
  proxy_http_version 1.1;
  proxy_set_header Host $host;
}
```

See `nginx-aptop.snippet.conf` for the full snippet (home root + Netty).

## Build on the server

After clone / pull of this branch (or main once merged):

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd /home/michal/ver/laptop

# Netty lib+exe only — avoid a full Mathlib-heavy default build if possible
lake build netty
# Prefer:
lake build netty && (cd netty-web && npm ci && npm run build)
```

Runtime:

- Node ≥ 18 (box has v20); `npm` only for the TypeScript build of `netty-web`
- elan / Lean `v4.35.0-rc1` per `lean-toolchain`
- `npm run build` writes `netty-web/dist/` (`server.js`, `js/client.js`, …)

### Publish / working tree

Serve from the **git tree** — no rsync of dist-only needed if Node serves
`public/` + `dist/js`. Systemd `WorkingDirectory=…/netty-web`,
`ExecStart=/usr/bin/node dist/server.js`.

### `NETTY_CMD`

Prefer the built binary so systemd does **not** invoke `lake` on every restart
(faster, less RAM spike):

```
Environment=NETTY_CMD=/home/michal/ver/laptop/.lake/build/bin/netty --serve
```

Fallback if the binary is missing: `lake exe netty --serve` (slower cold start).

## systemd

Units live in this directory:

- `aptop-netty.service` — install as a **system** unit with `User=michal`
  (same pattern as ofcp), or document `systemctl --user` if you prefer a user
  session. Cornerbot / host uses user `michal`.
- `aptop-interp.service` — **stub only**; wrapper not ready. Do not enable.
  Notes live here and in that file’s comments.

```bash
sudo cp deploy/aptop/aptop-netty.service /etc/systemd/system/
sudo systemctl daemon-reload
sudo systemctl enable --now aptop-netty.service
# systemctl status aptop-netty
```

Confirm `node` path (`which node` → often `/usr/bin/node`). Adjust
`ExecStart` if needed.

## MemoryMax / disk

| Concern | Guidance |
|---------|----------|
| Netty Node + Mathlib-free kernel | ~512 M–1 G in practice; **`MemoryMax=768M`** on `aptop-netty` |
| Full `lake build` of LaPToP / interp | Needs mathlib oleans via `lake exe cache get` and far more RAM — **do not** on this 4 GB box for v1 |
| Disk | Do not copy mathlib sources unnecessarily; use `lake exe cache get` for any LaPToP build |

Warn: a full Mathlib build will thrash this box. v1 ships home + Netty only.

## CodeMirror (interpreter language)

Under `deploy/aptop/site/js/aptop.js`: CDN-based highlighter (no npm of
CodeMirror into the Lean repo). Keywords from
`LaPToP/ProgramTheory/InterpreterLangSyntax.lean` `keywords`; `--` line
comments; operators `:=`, `==`, `-->`, `<--`, `=>`, `||`, `;..`, `/\`, `\/`,
`⇐`, `⇒`, etc. Wired into `/interp/` and `/examples/`. UI copy shows glyphs and plain names (Symbols sheet); no “backslash codes” jargon.

## Clone notes for cornerbot

```bash
# on 45.79.174.182 as michal
cd /home/michal/ver
git clone https://github.com/tangentproofs/laptop.git   # or git@github.com:tangentproofs/laptop.git
# or: pull feat/aptop-site for this PR before merge
cd laptop
git fetch origin feat/aptop-site && git checkout feat/aptop-site
export PATH="$HOME/.elan/bin:$PATH"
lake build netty
(cd netty-web && npm ci && npm run build)
# install nginx snippet + aptop-netty.service; do not enable aptop-interp
```

## Deferred (v1)

- Full interactive apply for program-theory `.calc` steps that need assignment/ok laws the session may not have (falls back to `direct` so the proof pane still fills)
- Building `interp` / LaPToP+Mathlib on the aptop box
- Optional Netty law/calc TextMate-style highlighter
- `/docs/` Verso/blueprint site

