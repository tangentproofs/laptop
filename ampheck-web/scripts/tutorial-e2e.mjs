// Play every tutorial lesson end to end in a real browser against a running
// ampheck-web (and so the real kernel), clicking only what the tutorial makes
// pulse. Each step must be judged done from the kernel's answer, or this fails.
//
//   npm run build && AMPHECK_PORT=4799 npm start &      # in ampheck-web/
//   node scripts/tutorial-e2e.mjs http://127.0.0.1:4799/ [shots-dir]
//
// Playwright is not a dependency of this package (the server must not need
// it); resolve it from anywhere, e.g. NODE_PATH=/path/to/node_modules.
// PW_CHROME=/usr/bin/google-chrome uses an installed Chrome.
import { createRequire } from 'node:module';
import { mkdirSync } from 'node:fs';

const require = createRequire(import.meta.url);
const { chromium, devices } = require('playwright');

const base = process.argv[2] ?? 'http://127.0.0.1:4799/';
const shots = process.argv[3] ?? '';
if (shots) mkdirSync(shots, { recursive: true });

const browser = await chromium.launch(process.env.PW_CHROME ? { executablePath: process.env.PW_CHROME } : {});
let failures = 0;
const log = (...a) => console.log(...a);

async function card(page) {
  return page.locator('section.tutorial');
}

/** Wait until the card shows a different step, or success, or a warning. */
async function waitMove(page, before) {
  await page.waitForFunction((b) => {
    const c = document.querySelector('section.tutorial');
    if (!c) return false;
    const now = `${c.getAttribute('data-lesson')}/${c.getAttribute('data-step')}/${c.querySelector('.tut-success') ? 'ok' : ''}/${c.querySelector('.tut-warn') ? 'warn' : ''}`;
    return now !== b;
  }, before, { timeout: 20000 });
}

async function where(page) {
  return page.evaluate(() => {
    const c = document.querySelector('section.tutorial');
    if (!c) return 'none';
    return `${c.getAttribute('data-lesson')}/${c.getAttribute('data-step')}/${c.querySelector('.tut-success') ? 'ok' : ''}/${c.querySelector('.tut-warn') ? 'warn' : ''}`;
  });
}

async function playLesson(page, n, tag, opts = {}) {
  log(`[${tag}] lesson ${n}`);
  for (let guard = 0; guard < 30; guard++) {
    const w = await where(page);
    if (w.includes('/ok/')) {
      if (shots) await page.screenshot({ path: `${shots}/${tag}-lesson${n}-done.png` });
      log(`  done: ${w}`);
      return true;
    }
    if (w.endsWith('warn')) {
      log(await page.evaluate(async () => {
        const r = await fetch('api', { method: 'POST', body: JSON.stringify({ op: 'state' }) });
        const j = await r.json();
        return JSON.stringify(j.state.lines.map((l) => [l.index, l.depth, l.expr, l.note, l.gap, l.focused]));
      }));
      throw new Error(`off the path at ${w}`);
    }
    const c = await card(page);
    // A lesson that pulses only on request.
    const showMe = c.locator('button.tut-small', { hasText: /^show me$/ });
    if (await showMe.count()) { await showMe.click(); await page.waitForTimeout(100); }
    const cta = c.locator('.tut-cta');
    if (await cta.count()) {
      if (shots && opts.shotSteps?.includes(guard)) {
        await page.screenshot({ path: `${shots}/${tag}-lesson${n}-step${guard + 1}.png` });
      }
      await cta.first().click();
    } else {
      const t = page.locator('.tut-target:not(.pane):not(.outcome):not(.line)');
      await t.first().waitFor({ timeout: 10000 });
      if (shots && opts.shotSteps?.includes(guard)) {
        await page.waitForTimeout(150);
        await page.screenshot({ path: `${shots}/${tag}-lesson${n}-step${guard + 1}.png` });
      }
      const tagName = await t.first().evaluate((e) => e.tagName);
      if (tagName === 'INPUT') {
        await t.first().fill('q');
        if (opts.holeShot && shots) await page.screenshot({ path: `${shots}/${tag}-lesson${n}-holebox.png` });
        await page.locator('.holes button[type="submit"]').click();
      } else {
        log('  click', w, (await t.first().getAttribute('data-law')) ?? (await t.first().getAttribute('data-tut')) ?? (await t.first().getAttribute('title')), (await t.first().getAttribute('data-result')) ?? '');
        await t.first().click();
        // Opening the small box of a greyed row moves the pulse, not the step.
        if (await page.locator('.holes').count()) continue;
      }
    }
    await waitMove(page, w);
  }
  throw new Error(`lesson ${n} did not finish`);
}

async function run(tag, ctxOpts, shotsFor) {
  const ctx = await browser.newContext(ctxOpts);
  const page = await ctx.newPage();
  page.on('pageerror', (e) => { failures++; log('page error', String(e)); });
  await page.goto(base);
  await page.evaluate(() => localStorage.removeItem('ampheck-tutorial-v1'));
  await page.goto(base + '#tutorial');
  await page.locator('section.tutorial').waitFor();
  await page.waitForSelector('[data-tut="start"]');
  if (shots && shotsFor.has(1)) await page.screenshot({ path: `${shots}/${tag}-lesson1-step1.png` });
  for (let n = 1; n <= 8; n++) {
    if (n > 1) {
      // A locked lesson cannot be opened ahead of time.
      const before = await where(page);
      await page.locator('.tutorial .tut-cta').click();
      await waitMove(page, before);
    }
    await playLesson(page, n, tag, {
      shotSteps: !shotsFor.has(n) ? [] : n === 7 ? [0, 2, 3] : n === 1 ? [1] : n === 5 ? [0, 1] : [0],
      holeShot: n === 4,
    });
    // The kernel itself says what was proved.
    log('  kernel:', (await page.locator('.pane.proof .outcome').textContent())?.trim());
  }
  const saved = await page.evaluate(() => localStorage.getItem('ampheck-tutorial-v1'));
  log(`[${tag}] progress:`, saved);
  if (!saved || JSON.parse(saved).done.length !== 8) { failures++; log('progress not saved'); }
  await ctx.close();
}

async function offPath() {
  const ctx = await browser.newContext({ viewport: { width: 1400, height: 900 } });
  const page = await ctx.newPage();
  await page.goto(base);
  await page.evaluate(() => localStorage.setItem('ampheck-tutorial-v1', JSON.stringify({ done: ['panes', 'one-law'], lesson: 2 })));
  await page.goto(base + '#tutorial-3');
  await page.locator('.tutorial[data-lesson="3"]').waitFor();
  await page.waitForSelector('.tut-target.suggestion');
  // The other duality row: a correct step, but not this lesson's.
  const wrong = page.locator('.suggestion[data-law="duality"][data-result="¬b ∨ ¬a"]');
  let w = await where(page);
  await wrong.click();
  await waitMove(page, w);
  if (!(await where(page)).endsWith('warn')) { failures++; log('off-path not detected'); }
  if (!(await page.locator('[data-tut="undo"].tut-target').count())) { failures++; log('undo not pulsed'); }
  if (shots) await page.screenshot({ path: `${shots}/desktop-offpath.png` });
  w = await where(page);
  await page.keyboard.press('u');
  await waitMove(page, w);
  if ((await where(page)).endsWith('warn')) { failures++; log('undo did not clear off-path'); }
  // A locked lesson: lesson 5 is not open yet.
  await page.locator('.tutorial button', { hasText: /^lessons$/ }).click();
  const locked = await page.locator('.tut-lesson[disabled]').count();
  log('[offpath] ok; locked lessons shown:', locked);
  if (locked !== 5) { failures++; log('expected 5 locked lessons'); }
  if (shots) await page.screenshot({ path: `${shots}/desktop-lesson-list.png` });
  await ctx.close();
}

try {
  await run('desktop', { viewport: { width: 1400, height: 900 } }, new Set([1, 2, 3, 4, 5, 6, 7, 8]));
  await offPath();
  await run('mobile', { ...devices['Pixel 7'] }, new Set([1, 5]));
} catch (e) {
  failures++;
  log('FAIL', e);
}
await browser.close();
log(failures === 0 ? 'ALL LESSONS PASS' : `${failures} failure(s)`);
process.exit(failures === 0 ? 0 : 1);
