/**
 * Interpreter web wrapper: loopback only, mirrors netty-web.
 * POST /run { program?, args?, demo? } → spawn interp with timeout.
 * If the binary is missing, answers with ok:false stub (UI still works).
 */
import { createServer, type IncomingMessage, type ServerResponse } from 'node:http';
import { spawn } from 'node:child_process';
import { access, writeFile, unlink } from 'node:fs/promises';
import { join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { tmpdir } from 'node:os';
import { randomBytes } from 'node:crypto';

const dist = fileURLToPath(new URL('.', import.meta.url));
const pkgRoot = resolve(dist, '..');
const repoRoot = resolve(process.env.INTERP_CWD ?? join(pkgRoot, '..'));

const host = process.env.INTERP_HOST ?? '127.0.0.1';
const port = Number(process.env.INTERP_PORT ?? 4712);
const bin =
  process.env.INTERP_BIN ?? join(repoRoot, '.lake/build/bin/interp');
const timeoutMs = Number(process.env.INTERP_TIMEOUT_MS ?? 15_000);
const maxBody = 200_000;

function body(req: IncomingMessage): Promise<string> {
  return new Promise((resolveP, reject) => {
    let text = '';
    req.setEncoding('utf8');
    req.on('data', (chunk: string) => {
      text += chunk;
      if (text.length > maxBody) reject(new Error('request too large'));
    });
    req.on('end', () => resolveP(text));
    req.on('error', reject);
  });
}

function sendJson(res: ServerResponse, code: number, value: unknown): void {
  const text = JSON.stringify(value);
  res.writeHead(code, {
    'content-type': 'application/json; charset=utf-8',
    'content-length': Buffer.byteLength(text),
  });
  res.end(text);
}

async function binExists(): Promise<boolean> {
  try {
    await access(bin);
    return true;
  } catch {
    return false;
  }
}

/** Parse "x=12 y=18" or "--n=10" into argv tokens. */
function parseArgs(args: string): string[] {
  const out: string[] = [];
  for (const tok of args.trim().split(/\s+/).filter(Boolean)) {
    if (tok.startsWith('--')) out.push(tok);
    else if (/^[A-Za-z_][A-Za-z0-9_]*=/.test(tok)) out.push(`--${tok}`);
    else out.push(tok);
  }
  return out;
}

function runInterp(argv: string[], cwd: string): Promise<{
  code: number | null;
  stdout: string;
  stderr: string;
  timedOut: boolean;
}> {
  return new Promise((resolveP) => {
    const child = spawn(bin, argv, {
      cwd,
      env: { ...process.env, PATH: process.env.PATH },
      stdio: ['ignore', 'pipe', 'pipe'],
    });
    let stdout = '';
    let stderr = '';
    let timedOut = false;
    const timer = setTimeout(() => {
      timedOut = true;
      child.kill('SIGKILL');
    }, timeoutMs);
    child.stdout?.setEncoding('utf8');
    child.stderr?.setEncoding('utf8');
    child.stdout?.on('data', (c: string) => {
      stdout += c;
      if (stdout.length > 500_000) child.kill('SIGKILL');
    });
    child.stderr?.on('data', (c: string) => {
      stderr += c;
      if (stderr.length > 200_000) child.kill('SIGKILL');
    });
    child.on('close', (code) => {
      clearTimeout(timer);
      resolveP({ code, stdout, stderr, timedOut });
    });
    child.on('error', (e) => {
      clearTimeout(timer);
      resolveP({ code: 127, stdout: '', stderr: String(e), timedOut: false });
    });
  });
}

const server = createServer((req, res) => {
  void (async () => {
    const url = new URL(req.url ?? '/', `http://${req.headers.host ?? 'localhost'}`);
    // nginx strips /interp/api/ → we see /run or /
    if (url.pathname === '/run' || url.pathname === '/api/run') {
      if (req.method !== 'POST') {
        sendJson(res, 405, { ok: false, error: 'POST a program to /run' });
        return;
      }
      let asked: { program?: string; args?: string; demo?: string };
      try {
        asked = JSON.parse(await body(req)) as typeof asked;
      } catch (e) {
        sendJson(res, 400, { ok: false, error: `bad JSON: ${String(e)}` });
        return;
      }

      if (!(await binExists())) {
        sendJson(res, 200, {
          ok: false,
          stub: true,
          error:
            'interp binary not built on this host (.lake/build/bin/interp). ' +
            'UI is live; build off-box with MemoryMax=6G LAKE_NUM_JOBS=1, ' +
            'or: systemd-run -p MemoryMax=6G --uid=michal lake build interp',
          stdout: '',
          stderr: '',
          code: null,
        });
        return;
      }

      const argv: string[] = [];
      const demo = typeof asked.demo === 'string' ? asked.demo.trim() : '';
      const program = typeof asked.program === 'string' ? asked.program : '';
      const args = typeof asked.args === 'string' ? asked.args : '';

      let tmp: string | null = null;
      try {
        if (demo && !program.trim()) {
          argv.push(`--demo=${demo}`);
        } else if (program.trim()) {
          tmp = join(tmpdir(), `aptop-interp-${randomBytes(8).toString('hex')}.aptop`);
          await writeFile(tmp, program, 'utf8');
          argv.push(tmp);
        } else if (demo) {
          argv.push(`--demo=${demo}`);
        } else {
          sendJson(res, 400, { ok: false, error: 'provide program or demo' });
          return;
        }
        argv.push(...parseArgs(args));

        const result = await runInterp(argv, repoRoot);
        if (result.timedOut) {
          sendJson(res, 200, {
            ok: false,
            error: `interp timed out after ${timeoutMs}ms`,
            stdout: result.stdout,
            stderr: result.stderr,
            code: result.code,
          });
          return;
        }
        sendJson(res, 200, {
          ok: (result.code ?? 1) === 0,
          stdout: result.stdout,
          stderr: result.stderr,
          code: result.code,
        });
      } finally {
        if (tmp) await unlink(tmp).catch(() => undefined);
      }
      return;
    }

    if (url.pathname === '/health' || url.pathname === '/') {
      const exists = await binExists();
      sendJson(res, 200, {
        ok: true,
        service: 'aptop-interp',
        bin,
        binExists: exists,
        stub: !exists,
      });
      return;
    }

    res.writeHead(404, { 'content-type': 'text/plain; charset=utf-8' });
    res.end('not found');
  })();
});

server.listen(port, host, () => {
  process.stdout.write(
    `interp-web: http://${host}:${port}/  (bin: ${bin} in ${repoRoot})\n`,
  );
});

for (const signal of ['SIGINT', 'SIGTERM'] as const) {
  process.on(signal, () => {
    server.close(() => process.exit(0));
  });
}
