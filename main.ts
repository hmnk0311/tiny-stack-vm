// Tiny stack VM: an exact interpreter for make.fun's stack ISA.
// The design goal is fidelity to the reference semantics, especially the
// awkward corners: wrapping 32-bit arithmetic, unsigned operations read
// back as signed, shift counts masked to five bits, and every trap code
// delivered exactly, with output written before a trap kept intact.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

type Outcome = { bytes: Uint8Array; code: number };

// How many immediate bytes follow each opcode byte; -1 marks a bad opcode.
const IMM: number[] = (() => {
  const t = new Array<number>(256).fill(-1);
  const plain = [0x00, 0x03, 0x04, 0x05, 0x06, 0x07, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x20, 0x21, 0x22, 0x34, 0x40, 0x41, 0x50, 0x51, 0x52, 0x53];
  for (const op of plain) t[op] = 0;
  t[0x01] = 1;
  t[0x30] = 2; t[0x31] = 2; t[0x32] = 2; t[0x33] = 2;
  t[0x02] = 4;
  return t;
})();

// Net stack traffic per opcode, packed as pops * 8 + pushes.
const TRAFFIC: Record<number, number> = {
  0x01: 1, 0x02: 1, 0x52: 1,
  0x03: 8, 0x17: 9, 0x1b: 9, 0x40: 9, 0x50: 8, 0x51: 8, 0x53: 8, 0x31: 8, 0x32: 8,
  0x04: 10,
  0x05: 18, 0x41: 16,
  0x06: 19,
  0x07: 27,
};
const BINARY = new Set([0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x18, 0x19, 0x1a, 0x1c, 0x1d, 0x1e, 0x20, 0x21, 0x22]);

function run(prog: Uint8Array, input: Uint8Array): Outcome {
  const stack = new Int32Array(256);
  let sp = 0;
  const calls = new Int32Array(64);
  let csp = 0;
  const mem = new Int32Array(256);
  const out = new Uint8Array(65536);
  let olen = 0;
  let inAt = 0;
  let pc = 0;
  let steps = 0;
  const finish = (code: number): Outcome => ({ bytes: out.slice(0, olen), code });

  for (;;) {
    if (steps >= 1000000) return finish(10);
    if (pc < 0 || pc >= prog.length) return finish(9);
    const op = prog[pc];
    const imm = IMM[op];
    if (imm === -1) return finish(5);
    if (pc + imm >= prog.length) return finish(9);
    steps += 1;
    const traffic = BINARY.has(op) ? 17 : (TRAFFIC[op] ?? 0);
    const pops = traffic >> 3;
    const pushes = traffic & 7;
    if (sp < pops) return finish(2);
    if (sp - pops + pushes > 256) return finish(3);
    const next = pc + 1 + imm;
    pc = next;

    if (BINARY.has(op)) {
      const b = stack[sp - 1];
      const a = stack[sp - 2];
      let r = 0;
      if (op === 0x10) r = (a + b) | 0;
      else if (op === 0x11) r = (a - b) | 0;
      else if (op === 0x12) r = Math.imul(a, b);
      else if (op === 0x13) {
        if (b === 0) return finish(4);
        r = a === -2147483648 && b === -1 ? a : Math.trunc(a / b) | 0;
      } else if (op === 0x14) {
        if (b === 0) return finish(4);
        r = b === -1 ? 0 : (a % b) | 0;
      } else if (op === 0x15) {
        if (b === 0) return finish(4);
        r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
      } else if (op === 0x16) {
        if (b === 0) return finish(4);
        r = ((a >>> 0) % (b >>> 0)) | 0;
      }
      else if (op === 0x18) r = a & b;
      else if (op === 0x19) r = a | b;
      else if (op === 0x1a) r = a ^ b;
      else if (op === 0x1c) r = a << (b & 31);
      else if (op === 0x1d) r = a >> (b & 31);
      else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
      else if (op === 0x20) r = a === b ? 1 : 0;
      else if (op === 0x21) r = a < b ? 1 : 0;
      else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
      sp -= 1;
      stack[sp - 1] = r;
      continue;
    }

    switch (op) {
      case 0x00:
        return finish(0);
      case 0x01:
        stack[sp++] = (prog[next - 1] << 24) >> 24;
        break;
      case 0x02:
        stack[sp++] = prog[next - 4] | (prog[next - 3] << 8) | (prog[next - 2] << 16) | (prog[next - 1] << 24);
        break;
      case 0x03:
        sp -= 1;
        break;
      case 0x04:
        stack[sp] = stack[sp - 1];
        sp += 1;
        break;
      case 0x05: {
        const top = stack[sp - 1];
        stack[sp - 1] = stack[sp - 2];
        stack[sp - 2] = top;
        break;
      }
      case 0x06:
        stack[sp] = stack[sp - 2];
        sp += 1;
        break;
      case 0x07: {
        const first = stack[sp - 3];
        stack[sp - 3] = stack[sp - 2];
        stack[sp - 2] = stack[sp - 1];
        stack[sp - 1] = first;
        break;
      }
      case 0x17:
        stack[sp - 1] = (-stack[sp - 1]) | 0;
        break;
      case 0x1b:
        stack[sp - 1] = ~stack[sp - 1];
        break;
      case 0x30:
      case 0x31:
      case 0x32: {
        const rel = ((prog[next - 2] | (prog[next - 1] << 8)) << 16) >> 16;
        let jump = op === 0x30;
        if (op !== 0x30) {
          const v = stack[--sp];
          jump = op === 0x31 ? v === 0 : v !== 0;
        }
        if (jump) pc = next + rel;
        break;
      }
      case 0x33:
        if (csp >= 64) return finish(7);
        calls[csp++] = next;
        pc = prog[next - 2] | (prog[next - 1] << 8);
        break;
      case 0x34:
        if (csp === 0) return finish(8);
        pc = calls[--csp];
        break;
      case 0x40: {
        const addr = stack[sp - 1];
        if (addr < 0 || addr > 255) return finish(6);
        stack[sp - 1] = mem[addr];
        break;
      }
      case 0x41: {
        const addr = stack[sp - 1];
        if (addr < 0 || addr > 255) return finish(6);
        mem[addr] = stack[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: {
        const text = String(stack[sp - 1]);
        if (olen + text.length > 65536) return finish(11);
        sp -= 1;
        for (let i = 0; i < text.length; i++) out[olen++] = text.charCodeAt(i);
        break;
      }
      case 0x51:
        if (olen + 1 > 65536) return finish(11);
        out[olen++] = stack[--sp] & 255;
        break;
      case 0x52:
        stack[sp++] = inAt < input.length ? input[inAt++] : -1;
        break;
      case 0x53:
        return finish(stack[--sp] & 255);
      default:
        return finish(5);
    }
  }
}

const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(IN_DIR).sort()) {
  const prog = new Uint8Array(readFileSync(join(IN_DIR, id, 'program.bin')));
  const input = new Uint8Array(readFileSync(join(IN_DIR, id, 'input.bin')));
  const result = run(prog, input);
  mkdirSync(join(OUT_DIR, id), { recursive: true });
  writeFileSync(join(OUT_DIR, id, 'stdout.bin'), result.bytes);
  writeFileSync(join(OUT_DIR, id, 'exit.txt'), `${result.code}\n`);
}
