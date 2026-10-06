# aptop.tangentcode.com — deploy notes

Lean deploy package for [aptop.tangentcode.com](https://aptop.tangentcode.com):
home, Netty under `/netty/`, Interpreter under `/interp/` (editable + Run).

Repo is **public**: `https://github.com/tangentproofs/laptop`. Checkout:

```
/home/michal/ver/laptop
```

Host: tangentcode Linode `45.79.174.182`.

## Canonical book + course (link prominently)

| What | URL |
|------|-----|
| aPToP book | https://www.cs.toronto.edu/~hehner/aPToP/ (also hehner.ca/aPToP) |
| PDF | https://www.cs.toronto.edu/~hehner/aPToP/aPToP.pdf |
| FMSD video course | https://www.cs.utoronto.ca/~hehner/FMSD/ (also hehner.ca/FMSD) |

Site header + hero on home / interp / examples / Netty must keep these visible.

## Public layout

| Path | What |
|------|------|
| `/` | Static home (`deploy/aptop/site/`) |
| `/netty/` | Netty three-pane UI (book .calc examples + demos) |
| `/interp/` | Editable CM6 editor + Run → `/interp/api/` |
| `/examples/` | Book-flavored snippets with `mountAptopEditor` + `\xx` |

## Upstreams (loopback only)

| Service | Bind | Notes |
|---------|------|-------|
| Netty Node | `127.0.0.1:4711` | `netty-web` + Lean kernel |
| Interp Node | `127.0.0.1:4712` | `interp-web` → `.lake/build/bin/interp` |

## Build

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd /home/michal/ver/laptop

lake build netty
(cd netty-web && npm ci && npm run build)
(cd interp-web && npm ci && npm run build)

# Interp binary (Mathlib-heavy). Prefer MemoryMax; skip if OOM:
sudo systemd-run --uid=michal -p MemoryMax=6G -p WorkingDirectory=/home/michal/ver/laptop \
  -E PATH="$HOME/.elan/bin:$PATH" -E LAKE_NUM_JOBS=1 \
  --wait lake build interp
# If killed: leave stub; interp-web still answers stub:true and UI works.
```

`NETTY_CMD` / `INTERP_BIN` prefer built binaries so systemd does not invoke `lake` on restart.

## systemd

```bash
sudo cp deploy/aptop/aptop-netty.service deploy/aptop/aptop-interp.service /etc/systemd/system/
sudo systemctl daemon-reload
sudo systemctl enable --now aptop-netty.service aptop-interp.service
```

Both units set `MemoryMax=768M`.

## nginx

See `nginx-aptop.snippet.conf`: `/netty/` → `:4711/`, `/interp/api/` → `:4712/`, `/` → `deploy/aptop/site`.

## Backslash expansions

`deploy/aptop/site/js/expansions.js` (ported from platform `web/js/expansions.mts`)
plus aPToP glyphs (`\=>` ⇒, `\impliedby` ⇐, `\equiv` ≡, `\times` ×, `\cdot` ·, `\prime` ′, …).
Wired in `mountAptopEditor` via CM6 `inputHandler`.

## Netty demos

Dropdown **book examples…** loads `netty-web/public/examples/*.calc` from
`LaPToP/Exercises/calc` (ex121, ex136–137, sum, ex139). **demonstration…**
keeps live kernel demos with **portation** first; gap/fold/merge secondary.
