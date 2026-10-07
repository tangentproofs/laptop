#!/usr/bin/env node
/**
 * Audit public/examples/*.calc + picker demos: every apply must succeed, no gaps.
 * Run after `npm run build` with netty binary available.
 */
import { spawn } from 'node:child_process';
import { readFileSync, readdirSync, writeFileSync, existsSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const here = dirname(fileURLToPath(import.meta.url));
const webRoot = resolve(here, '..');
const repoRoot = resolve(webRoot, '..');
const examplesDir = join(webRoot, 'public/examples');
const calcLoadPath = join(webRoot, 'public/js/calc-load.js');
if (!existsSync(calcLoadPath)) {
  console.error('Build client first: (cd netty-web && npm run build)');
  process.exit(2);
}
const { parseCalcTheorems, theoremToScript, scriptFailureReason, BOOK_CALCS, PICKER_EXAMPLES } =
  await import(pathToFileURL(calcLoadPath).href);

const nettyBin = process.env.NETTY_BIN || join(repoRoot, '.lake/build/bin/netty');
if (!existsSync(nettyBin)) {
  console.error('Missing netty binary at', nettyBin, '(lake build netty)');
  process.exit(2);
}

class Kernel {
  constructor() {
    this.child = spawn(nettyBin, ['--serve'], { cwd: repoRoot, stdio: ['pipe', 'pipe', 'pipe'] });
    this.pending = new Map();
    this.next = 1;
    this.buf = '';
    this.dead = null;
    this.child.stdout.setEncoding('utf8');
    this.child.stdout.on('data', (c) => this.recv(c));
    this.child.stderr.on('data', () => {});
    this.child.on('exit', (code) => { this.dead = new Error(`exit ${code}`); });
  }
  recv(chunk) {
    this.buf += chunk;
    let at;
    while ((at = this.buf.indexOf('\n')) >= 0) {
      const line = this.buf.slice(0, at).trim();
      this.buf = this.buf.slice(at + 1);
      if (!line) continue;
      let ans;
      try { ans = JSON.parse(line); } catch { continue; }
      const w = this.pending.get(ans.id);
      if (w) { this.pending.delete(ans.id); w(ans); }
    }
  }
  request(op, arg = '') {
    if (this.dead) return Promise.reject(this.dead);
    const id = this.next++;
    return new Promise((resolve, reject) => {
      const t = setTimeout(() => reject(new Error('timeout')), 30000);
      this.pending.set(id, (ans) => { clearTimeout(t); resolve(ans); });
      this.child.stdin.write(JSON.stringify({ id, op, arg }) + '\n', (e) => { if (e) reject(e); });
    });
  }
  kill() { try { this.child.kill(); } catch {} }
}

async function replay(k, lines) {
  await k.request('reset');
  for (const line of lines) {
    const t = line.trim();
    if (!t || t.startsWith('#')) continue;
    const word = t.split(/\s+/)[0];
    if (word === 'proof' || word === 'suggest' || word === 'context') continue;
    const a = await k.request('cmd', t);
    if (!a.ok) return { ok: false, err: a.error || JSON.stringify(a), line: t };
  }
  const st = await k.request('state');
  const state = st.state || st;
  const gaps = (state?.lines || []).filter((l) => l.gap);
  if (gaps.length) return { ok: false, err: `gaps on lines ${gaps.map((g) => g.index).join(',')}`, line: '' };
  return { ok: true };
}

const files = readdirSync(examplesDir).filter((f) => f.endsWith('.calc')).sort();
const pickerIds = new Set(BOOK_CALCS.map((b) => b.id));
const rows = [];
console.log('netty:', nettyBin);
const k = new Kernel();
await k.request('reset');

for (const file of files) {
  const id = file.replace(/\.calc$/, '');
  const text = readFileSync(join(examplesDir, file), 'utf8');
  const ths = parseCalcTheorems(text);
  if (ths.length === 0) {
    rows.push({ id, inPicker: pickerIds.has(id), status: 'FAIL', reason: 'no theorem/refine' });
    console.log('FAIL', id, 'no theorem');
    continue;
  }
  const th = ths[0];
  const why = scriptFailureReason(th);
  if (why) {
    rows.push({ id, inPicker: pickerIds.has(id), status: 'FAIL', reason: why });
    console.log('FAIL', id, why);
    continue;
  }
  const script = theoremToScript(th, true);
  const r = await replay(k, script);
  rows.push({ id, inPicker: pickerIds.has(id), status: r.ok ? 'PASS' : 'FAIL',
    reason: r.ok ? 'every apply ok, no gaps' : `${r.err}${r.line ? ' @ ' + r.line : ''}` });
  console.log(r.ok ? 'PASS' : 'FAIL', id, rows.at(-1).reason);
}

for (const ex of PICKER_EXAMPLES.filter((e) => e.kind === 'demo')) {
  await k.request('reset');
  const a = await k.request('demo', ex.id);
  if (!a.ok) {
    rows.push({ id: `demo:${ex.id}`, inPicker: true, status: 'FAIL', reason: a.error || 'demo failed' });
    console.log('FAIL', `demo:${ex.id}`);
    continue;
  }
  const st = await k.request('state');
  const state = st.state || st;
  const gaps = (state?.lines || []).filter((l) => l.gap);
  const ok = gaps.length === 0;
  rows.push({ id: `demo:${ex.id}`, inPicker: true, status: ok ? 'PASS' : 'FAIL',
    reason: ok ? 'demo, no gaps' : `gaps ${gaps.map((g) => g.index).join(',')}` });
  console.log(ok ? 'PASS' : 'FAIL', `demo:${ex.id}`);
}
k.kill();

const md = ['# Netty examples step-validity audit', '',
  'Source of truth for inventory/blockers: [`BOOK-CENSUS.md`](BOOK-CENSUS.md).',
  'Hierarchical picker: `public/examples/manifest.json`.',
  '',
  '| id | in picker | status | reason |',
  '|----|-----------|--------|--------|',
  ...rows.map((r) => `| \`${r.id}\` | ${r.inPicker ? 'yes' : 'no'} | **${r.status}** | ${String(r.reason).replace(/\|/g, '/')} |`),
  ''];
writeFileSync(join(webRoot, 'AUDIT-CALCS.md'), md.join('\n'));
const bad = rows.filter((r) => r.inPicker && r.status === 'FAIL');
if (bad.length) {
  console.error('PICKER FAIL:', bad.map((r) => r.id).join(', '));
  process.exit(1);
}
console.log('All picker entries PASS.');
