/**
 * The kernel as a child process.
 *
 * `lake exe netty --serve` reads one JSON request per line and writes one
 * line of JSON per answer, so talking to it is: keep the process, number the
 * requests, and hand each answer to whoever is waiting for that number.
 */

import { spawn, type ChildProcessWithoutNullStreams } from 'node:child_process';
import type { Op, Request, Response } from './protocol.js';

/** What a request that is still outstanding is waiting on. */
interface Pending {
  resolve: (r: Response) => void;
  reject: (e: Error) => void;
}

/** A running `netty --serve`. */
export class Kernel {
  private child: ChildProcessWithoutNullStreams;
  private pending = new Map<number, Pending>();
  private next = 1;
  private buffer = '';
  private dead: Error | null = null;

  constructor(command: string, args: string[], cwd: string) {
    this.child = spawn(command, args, { cwd, stdio: ['pipe', 'pipe', 'pipe'] });
    this.child.stdout.setEncoding('utf8');
    this.child.stdout.on('data', (chunk: string) => this.receive(chunk));
    this.child.stderr.setEncoding('utf8');
    // The kernel's own complaints (a bad law file, a missing build) are the
    // server's log; they are not answers to a request.
    this.child.stderr.on('data', (chunk: string) => process.stderr.write(chunk));
    this.child.on('error', (e: Error) => this.die(e));
    this.child.on('exit', (code: number | null, signal: string | null) =>
      this.die(new Error(`the kernel exited (code ${code}, signal ${signal})`)));
  }

  /** Split what has arrived into lines, and answer what each line answers. */
  private receive(chunk: string): void {
    this.buffer += chunk;
    let at: number;
    while ((at = this.buffer.indexOf('\n')) >= 0) {
      const line = this.buffer.slice(0, at).trim();
      this.buffer = this.buffer.slice(at + 1);
      if (line === '') continue;
      let answer: Response;
      try {
        answer = JSON.parse(line) as Response;
      } catch {
        process.stderr.write(`netty-web: the kernel said something that is not JSON: ${line}\n`);
        continue;
      }
      const waiting = this.pending.get(answer.id);
      if (waiting === undefined) {
        process.stderr.write(`netty-web: an answer to nothing: ${line}\n`);
        continue;
      }
      this.pending.delete(answer.id);
      waiting.resolve(answer);
    }
  }

  /** The kernel is gone: nobody's request will be answered. */
  private die(e: Error): void {
    if (this.dead !== null) return;
    this.dead = e;
    for (const waiting of this.pending.values()) waiting.reject(e);
    this.pending.clear();
  }

  /** Ask the kernel one thing. */
  request(op: Op, arg = ''): Promise<Response> {
    if (this.dead !== null) return Promise.reject(this.dead);
    const id = this.next++;
    const request: Request = { id, op, arg };
    return new Promise<Response>((resolve, reject) => {
      this.pending.set(id, { resolve, reject });
      this.child.stdin.write(JSON.stringify(request) + '\n', (e) => {
        if (e) {
          this.pending.delete(id);
          reject(e);
        }
      });
    });
  }

  /** Let the kernel see the end of its input, which is how it stops. */
  close(): void {
    this.child.stdin.end();
  }
}
