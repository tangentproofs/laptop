# netty-web — the three panes

A window over the Netty kernel: the **proof**, the **context** and the
**suggestions**, as the [Netty
document](https://www.cs.toronto.edu/~naiman/Netty_document.pdf) describes
them. It is a small TypeScript client and a small Node server, and it decides
nothing about a proof: the document model, the law matching, the suggestions,
the zoom stack and what a proof proves are all `Netty/` in Lean, reached
through `lake exe netty --serve`.

```text
browser  ──POST /api──▶  node dist/server.js  ──stdin/stdout──▶  lake exe netty --serve
   ▲                                                                      │
   └────────────────── one JSON answer: the whole session ◀───────────────┘
```

A click is one line of the kernel's own script language — a suggestion is
`apply #N`, a subexpression is `zoom N`, a line number is `focus N`, the next
line typed in is `direct = …` — so anything the window can do, a script can
do, and every change still goes through `Netty.Doc.step`.

## Running it

```bash
export PATH="$HOME/.elan/bin:$PATH"   # so that the server can run `lake`
lake build netty                      # a few seconds

cd netty-web
npm install                           # typescript and @types/node, nothing else
npm run serve                         # compile, then listen on 127.0.0.1:4173
```

Then open <http://127.0.0.1:4173/>. `npm run build` compiles without starting
the server, `npm start` starts it without compiling, and `npm run check` type
checks both halves. The server listens on the loopback interface only.

| variable | what it does | default |
| --- | --- | --- |
| `NETTY_PORT` | the port | `4173` |
| `NETTY_HOST` | the interface | `127.0.0.1` |
| `NETTY_CMD` | how to start the kernel | `lake exe netty --serve` |
| `NETTY_CWD` | where to start it | the repository root |

`NETTY_CMD` is how to add law files or skip `lake`:
`NETTY_CMD='.lake/build/bin/netty --serve --laws=my.laws'`.

## Using it

* **demonstration…** replays one of the kernel's demonstrations —
  `portation` is the document's own first example, `discharge` zooms in and
  uses the context, `gap` leaves a gap and then closes it, and `minimize`
  applies a law to a part of a line. **new** starts again with the same laws.
* **A click on a suggestion** writes that line. Greyed suggestions are the
  ones whose match left a law variable unconstrained; the kernel will not
  apply those, and says which variable it is.
* **A click on a subexpression** of the last line zooms in to it, which opens
  a subproof with its own direction and its own context. **zoom out** (`o`)
  closes it and puts the result back in the line it came from.
* **A click on a line number** moves the focus there. Any line of an open level
  will do: the kernel closes the subproofs below it, as zooming out would. A
  greyed number is a line of a subproof that has already been zoomed out of,
  which a click cannot re-open.
  Typing a line in the box at the focus is direct entry: it leaves a
  gap, marked `!`, until a suggestion that writes exactly that line closes it.
* **save** writes the proof file the kernel's `save` writes, and **load**
  reads one back. **panes: lines / panes: text** switches between the drawn
  panes and the same three panes as `lake exe netty` prints them.
* Keys: `0`–`9` take that suggestion, `u` undoes, `o` zooms out, `Enter` puts
  the cursor in the direct-entry box.

Expressions are the boolean and number fragment of aPToP, in the kernel's own
notation (`lake exe netty --help` gives the ASCII spellings: `~ /\ \/ => <=
== ==> <== =< >= != T F`).

## What is where

```text
src/protocol.ts   the shapes Netty/Api.lean writes: a line, a suggestion, the state
src/kernel.ts     `netty --serve` as a child process: number the requests, match the answers
src/server.ts     static files, and POST /api forwarding one request to the kernel
src/client.ts     the three panes, and a click as a line of the script language
public/           index.html, netty.css, and public/js/ from the compiler
```

`npm run build` writes `dist/` (the server) and `public/js/` (the client);
neither is checked in.

## What it does not do yet

The kernel's own residuals are listed in `.sci/netty-plan.md` and are visible
here: matching is modulo associativity but not modulo symmetry or an identity
element; and a law applies to the whole line and to each of its main operands,
but not to deeper subterms or to a contiguous segment of an association. There
is no ML ranking of the suggestions, no VS Code webview, and no editing of law
files from the window — laws are files, and `NETTY_CMD` is how to add one.

The document's two display collapses *are* done, in the kernel: a subproof that
is a single law application is drawn as its parent line with the law's name
moved up onto it, and two zoom-ins matched by two zoom-outs are drawn as one
zoom step. They arrive here as `state.lines` — the lines a collapse hides are
simply not in the answer, and a line it lifts arrives with a smaller `depth` —
so the window draws them without knowing they exist. The `fold` and `merge`
demonstrations show each of them.
