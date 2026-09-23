/**
 * The web server: static files, and one route that forwards a request to the
 * kernel and hands back its answer.
 *
 * It listens on the loopback interface only. A request it forwards can start a
 * proof, apply a law, zoom, undo, and carry the text of a proof file in and
 * out; it cannot ask the kernel to open a file, because the kernel refuses
 * that over this channel (`Netty/Api.lean`).
 */

import { createServer, type IncomingMessage, type ServerResponse } from 'node:http';
import { readFile } from 'node:fs/promises';
import { join, normalize, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { Kernel } from './kernel.js';
import { OPS, type Op } from './protocol.js';

const dist = fileURLToPath(new URL('.', import.meta.url));
const pkgRoot = resolve(dist, '..');
const repoRoot = resolve(pkgRoot, '..');
const publicDir = join(pkgRoot, 'public');

const host = process.env.NETTY_HOST ?? '127.0.0.1';
const port = Number(process.env.NETTY_PORT ?? 4173);
/** How to start the kernel; `NETTY_CMD` is split on spaces. */
const kernelCmd = (process.env.NETTY_CMD ?? 'lake exe netty --serve').split(/\s+/);
/** Where to run it: the repository, so that `--laws=` paths read as usual. */
const kernelCwd = process.env.NETTY_CWD ?? repoRoot;

const kernel = new Kernel(kernelCmd[0]!, kernelCmd.slice(1), kernelCwd);

const TYPES: Record<string, string> = {
  '.html': 'text/html; charset=utf-8',
  '.css': 'text/css; charset=utf-8',
  '.js': 'text/javascript; charset=utf-8',
  '.json': 'application/json; charset=utf-8',
  '.map': 'application/json; charset=utf-8',
};

/** Read the whole body of a request. */
function body(req: IncomingMessage): Promise<string> {
  return new Promise((resolve, reject) => {
    let text = '';
    req.setEncoding('utf8');
    req.on('data', (chunk: string) => {
      text += chunk;
      // A proof file arrives this way; nothing else here is large.
      if (text.length > 4_000_000) reject(new Error('the request is too large'));
    });
    req.on('end', () => resolve(text));
    req.on('error', reject);
  });
}

/** Answer with JSON. */
function sendJson(res: ServerResponse, code: number, value: unknown): void {
  const text = JSON.stringify(value);
  res.writeHead(code, {
    'content-type': 'application/json; charset=utf-8',
    'content-length': Buffer.byteLength(text),
  });
  res.end(text);
}

/** Serve a file from `public/`, with no way out of it. */
async function sendFile(res: ServerResponse, urlPath: string): Promise<void> {
  const wanted = urlPath === '/' ? '/index.html' : urlPath;
  const path = join(publicDir, normalize(wanted).replace(/^(\.\.[/\\])+/, ''));
  if (!path.startsWith(publicDir)) {
    res.writeHead(403).end('forbidden');
    return;
  }
  try {
    const bytes = await readFile(path);
    const dot = path.lastIndexOf('.');
    const type = TYPES[path.slice(dot)] ?? 'application/octet-stream';
    res.writeHead(200, { 'content-type': type, 'content-length': bytes.length });
    res.end(bytes);
  } catch {
    res.writeHead(404, { 'content-type': 'text/plain; charset=utf-8' });
    res.end('not found');
  }
}

const server = createServer((req: IncomingMessage, res: ServerResponse) => {
  void (async () => {
    const url = new URL(req.url ?? '/', `http://${req.headers.host ?? 'localhost'}`);
    if (url.pathname === '/api') {
      if (req.method !== 'POST') {
        sendJson(res, 405, { ok: false, error: 'the kernel is spoken to with POST' });
        return;
      }
      let asked: { op?: string; arg?: string };
      try {
        asked = JSON.parse(await body(req)) as { op?: string; arg?: string };
      } catch (e) {
        sendJson(res, 400, { ok: false, error: `that is not a request: ${String(e)}` });
        return;
      }
      if (typeof asked.op !== 'string' || !OPS.includes(asked.op as Op)) {
        sendJson(res, 400, { ok: false, error: `there is no request ‘${String(asked.op)}’` });
        return;
      }
      try {
        sendJson(res, 200, await kernel.request(asked.op as Op, asked.arg ?? ''));
      } catch (e) {
        sendJson(res, 502, { ok: false, error: `the kernel: ${String(e)}` });
      }
      return;
    }
    if (req.method !== 'GET' && req.method !== 'HEAD') {
      res.writeHead(405).end('method not allowed');
      return;
    }
    await sendFile(res, url.pathname);
  })();
});

server.listen(port, host, () => {
  process.stdout.write(`netty-web: http://${host}:${port}/  (kernel: ${kernelCmd.join(' ')} in ${kernelCwd})\n`);
});

for (const signal of ['SIGINT', 'SIGTERM'] as const) {
  process.on(signal, () => {
    kernel.close();
    server.close(() => process.exit(0));
  });
}
