# aptop.tangentcode.com — deploy notes

Lean deploy package for [aptop.tangentcode.com](https://aptop.tangentcode.com):
home + Ampheck under `/ampheck/`, the interpreter runner under `/interp/`.
This directory is the survey and the one path cornerbot / the Linode host should
follow. Do **not** build Mathlib-heavy Aptop/interp on the aptop box for v1.

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
| `/ampheck/` | Ampheck three-pane UI (Node + Lean kernel), labelled “Proof Assistant” on the site |
| `/interp/` | Editable CodeMirror runner + Symbols sheet; Run POSTs to `/interp/api/run` |
| `/examples/` | Redirects to `/interp/` (kept for old links; not in the nav) |
| `/ampheck/` book examples | `.calc` files under `ampheck-web/public/examples/` load into the proof pane |
| `/docs/` | Optional later |

## Upstreams (loopback only)

| Service | Bind | Notes |
|---------|------|-------|
| Ampheck Node | `127.0.0.1:4711` | Serves `ampheck-web/public/` + `POST /api` |
| interp-web Node | `127.0.0.1:4712` | `POST /run` → `.lake/build/bin/interp`; answers `stub:true` if the binary is absent |

## Architecture survey

### Ampheck — not pure static

1. Browser loads `public/index.html` (relative CSS/JS: `./ampheck.css`, `./js/client.js`).
2. Client `POST`s JSON to **`api` relative to the page URL** (see below).
3. Node (`ampheck-web/dist/server.js`) serves static files and forwards `/api` to a
   long-lived Lean kernel over stdin/stdout.
4. Kernel: `lake exe ampheck --serve` or, after build,
   `.lake/build/bin/ampheck --serve`. **Ampheck has no Mathlib dependency.**

### Interpreter — static page + small Node wrapper

1. `/interp/` is static (`deploy/aptop/site/interp/`), served by nginx's `location /`.
2. Its Run button POSTs `{program, args, demo}` to **`api/run` relative to the
   page**, i.e. `/interp/api/run`.
3. nginx strips `/interp/api/` and proxies to `interp-web` (`interp-web/dist/server.js`,
   `aptop-interp.service`) on `127.0.0.1:4712`, which sees `/run`.
4. interp-web writes the program to a temp file and runs
   `.lake/build/bin/interp FILE --x=12 …` with a 15 s timeout. If the binary
   is missing it still answers 200 with `{ok:false, stub:true, error:…}`, so the
   page shows a clear message instead of a 502. `GET /health` reports `binExists`.
- The interp binary needs Aptop + Mathlib oleans (`lake exe cache get`, then
  `lake build interp`). Do **not** build it on this box unless necessary
  (RAM/disk); without it the runner is in stub mode.

## Critical: Ampheck under `/ampheck/`

The client used to `fetch('/api', …)`, which breaks when the UI is served at
`https://aptop.tangentcode.com/ampheck/` (would hit site root `/api`).

It now resolves the API path from the page URL:

```ts
function apiUrl(): string {
  const base = window.location.pathname.endsWith('/')
    ? window.location.pathname
    : window.location.pathname.replace(/\/[^/]*$/, '/');
  return new URL('api', window.location.origin + base).pathname;
}
```

So at `/ampheck/` (or `/ampheck/index.html`) the browser POSTs to **`/ampheck/api`**.

Nginx must **strip the `/ampheck/` prefix** when proxying so the Node server still
sees `/` and `/api`:

```nginx
location /ampheck/ {
  proxy_pass http://127.0.0.1:4711/;  # trailing slash strips /ampheck/
  proxy_http_version 1.1;
  proxy_set_header Host $host;
}
```

See `nginx-aptop.snippet.conf` for the full snippet (home root + Ampheck).

## Migrating from Netty → Ampheck (one-time)

Our calculational proof tool was renamed **Netty → Ampheck**. Ampheck is
inspired by Netty, the calculational prover's assistant designed by Eric
Hehner, Robert Will, Lev Naiman, David Kordalewski and others at the
University of Toronto (named for Netty van Gasteren); see
[the Netty document](https://www.cs.toronto.edu/~hehner/Netty.pdf).
The Lean library was renamed **LaPToP → Aptop** at the same time.

| Was | Now |
|-----|-----|
| `netty-web/` | `ampheck-web/` |
| `lake build netty`, `.lake/build/bin/netty` | `lake build ampheck`, `.lake/build/bin/ampheck` |
| `aptop-netty.service` | `aptop-ampheck.service` (same port `4711`) |
| `NETTY_HOST/PORT/CMD/CWD` env | `AMPHECK_HOST/PORT/CMD/CWD` |
| `/netty/`, `/netty/api` | `/ampheck/`, `/ampheck/api` (old URLs redirect: 301 pages, 308 API) |

```bash
cd /home/michal/ver/laptop
git fetch origin feat/aptop-site && git checkout feat/aptop-site && git pull --ff-only
export PATH="$HOME/.elan/bin:$PATH"
lake build ampheck
(cd ampheck-web && npm ci && npm run build)
rm -rf netty-web            # leftover untracked node_modules/dist, if any
sudo systemctl disable --now aptop-netty.service
sudo rm /etc/systemd/system/aptop-netty.service
sudo cp deploy/aptop/aptop-ampheck.service /etc/systemd/system/
sudo systemctl daemon-reload
sudo systemctl enable --now aptop-ampheck.service
# replace the old `location /netty/` block with nginx-aptop.snippet.conf
sudo nginx -t && sudo systemctl reload nginx
curl -s -XPOST https://aptop.tangentcode.com/ampheck/api -d '{"op":"reset"}'   # ok:true
curl -sI https://aptop.tangentcode.com/netty/ | head -3                        # 301 -> /ampheck/
```

## Build on the server

After clone / pull of this branch (or main once merged):

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd /home/michal/ver/laptop

# Ampheck lib+exe only — avoid a full Mathlib-heavy default build if possible
lake build ampheck
# Prefer:
lake build ampheck && (cd ampheck-web && npm ci && npm run build)
(cd interp-web && npm ci && npm run build)   # the /interp/api wrapper
```

Runtime:

- Node ≥ 18 (box has v20); `npm` only for the TypeScript build of `ampheck-web`
- elan / Lean `v4.35.0-rc1` per `lean-toolchain`
- `npm run build` writes `ampheck-web/dist/` (`server.js`, `js/client.js`, …)

### Publish / working tree

Serve from the **git tree** — no rsync of dist-only needed if Node serves
`public/` + `dist/js`. Systemd `WorkingDirectory=…/ampheck-web`,
`ExecStart=/usr/bin/node dist/server.js`.

### `AMPHECK_CMD`

Prefer the built binary so systemd does **not** invoke `lake` on every restart
(faster, less RAM spike):

```
Environment="AMPHECK_CMD=/home/michal/ver/laptop/.lake/build/bin/ampheck --serve"
```

Fallback if the binary is missing: `lake exe ampheck --serve` (slower cold start).

## systemd

Units live in this directory:

- `aptop-ampheck.service` — install as a **system** unit with `User=michal`
  (same pattern as ofcp), or document `systemctl --user` if you prefer a user
  session. Cornerbot / host uses user `michal`.
- `aptop-interp.service` — runs `interp-web` (`WorkingDirectory=…/interp-web`,
  `ExecStart=/usr/bin/node dist/server.js`). Build it first with
  `(cd interp-web && npm ci && npm run build)`; without `dist/server.js` the
  unit crash-loops and `/interp/api` returns 502.

```bash
sudo cp deploy/aptop/aptop-ampheck.service deploy/aptop/aptop-interp.service /etc/systemd/system/
sudo systemctl daemon-reload
sudo systemctl enable --now aptop-ampheck.service aptop-interp.service
# systemctl status aptop-ampheck aptop-interp
curl -s http://127.0.0.1:4712/health        # ok:true, binExists true/false
curl -s -XPOST https://aptop.tangentcode.com/interp/api/run -d '{"demo":"gcd"}'
```

Confirm `node` path (`which node` → often `/usr/bin/node`). Adjust
`ExecStart` if needed.

## MemoryMax / disk

| Concern | Guidance |
|---------|----------|
| Ampheck Node + Mathlib-free kernel | ~512 M–1 G in practice; **`MemoryMax=768M`** on `aptop-ampheck` |
| `lake build ampheck` | Under a minute; `Ampheck/Replay.lean` alone is ~7 s and ~110 MB of anonymous memory |
| `lake build AmpheckReplay` (also in plain `lake build`) | The replays against the shipped laws: minutes and ~3 GB per module — **do not** build on this box; `ampheck` does not need it |
| Full `lake build` of Aptop / interp | Needs mathlib oleans via `lake exe cache get` and far more RAM — **do not** on this 4 GB box for v1 |
| Disk | Do not copy mathlib sources unnecessarily; use `lake exe cache get` for any Aptop build |

Warn: a full Mathlib build will thrash this box. v1 ships home + Ampheck only.

## CodeMirror (interpreter language)

Under `deploy/aptop/site/js/aptop.js`: CDN-based highlighter (no npm of
CodeMirror into the Lean repo). Keywords from
`Aptop/ProgramTheory/InterpreterLangSyntax.lean` `keywords`; `--` line
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
lake build ampheck
(cd ampheck-web && npm ci && npm run build)
(cd interp-web && npm ci && npm run build)
# install nginx snippet + aptop-ampheck.service + aptop-interp.service
```

## Deferred (v1)

- Full interactive apply for program-theory `.calc` steps that need assignment/ok laws the session may not have (falls back to `direct` so the proof pane still fills)
- Building `interp` / Aptop+Mathlib on the aptop box
- Optional Ampheck law/calc TextMate-style highlighter
- `/docs/` Verso/blueprint site

