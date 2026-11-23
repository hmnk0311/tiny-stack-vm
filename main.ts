// Exact tiny stack VM, compact form: same step order, traps and wrapping
// as the reference. Per step: step limit, pc range, opcode, immediate fit,
// then stack needs, then the instruction's own trap, then its effect.
import { readdirSync, readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { join } from 'node:path';
type R = { out: Uint8Array; code: number };
function run(p: Uint8Array, inp: Uint8Array): R {
  const D = new Int32Array(256), C = new Int32Array(64), M = new Int32Array(256), O = new Uint8Array(65536);
  let sp = 0, cp = 0, pc = 0, st = 0, ol = 0, ip = 0;
  const done = (code: number): R => ({ out: O.slice(0, ol), code });
  while (true) {
    if (st >= 1000000) return done(10);
    if (pc < 0 || pc >= p.length) return done(9);
    const op = p[pc];
    if (!(op < 8 || (op >= 16 && op <= 34) || (op >= 48 && op <= 52) || op == 64 || op == 65 || (op >= 80 && op <= 83))) return done(5);
    const im = op == 1 ? 1 : op == 2 ? 4 : op >= 48 && op <= 51 ? 2 : 0;
    if (pc + im >= p.length) return done(9);
    let po = 0, pu = 0;
    if ((op >= 16 && op <= 22) || (op >= 24 && op <= 26) || (op >= 28 && op <= 30) || (op >= 32 && op <= 34)) { po = 2; pu = 1; }
    else if (op == 23 || op == 27 || op == 64) { po = 1; pu = 1; }
    else if (op == 3 || op == 49 || op == 50 || op == 80 || op == 81 || op == 83) po = 1;
    else if (op == 1 || op == 2 || op == 82) pu = 1;
    else if (op == 4) { po = 1; pu = 2; }
    else if (op == 5) { po = 2; pu = 2; }
    else if (op == 6) { po = 2; pu = 3; }
    else if (op == 7) { po = 3; pu = 3; }
    else if (op == 65) po = 2;
    st++;
    if (sp < po) return done(2);
    if (sp - po + pu > 256) return done(3);
    const b1 = p[pc + 1], b2 = p[pc + 2], nx = pc + 1 + im;
    pc = nx;
    if (po == 2 && pu == 1) {
      const b = D[sp - 1], a = D[sp - 2];
      let r = 0;
      switch (op) {
        case 16: r = a + b | 0; break;
        case 17: r = a - b | 0; break;
        case 18: r = Math.imul(a, b); break;
        case 19: if (b == 0) return done(4); r = a == -2147483648 && b == -1 ? a : Math.trunc(a / b) | 0; break;
        case 20: if (b == 0) return done(4); r = b == -1 ? 0 : a % b | 0; break;
        case 21: if (b == 0) return done(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; break;
        case 22: if (b == 0) return done(4); r = (a >>> 0) % (b >>> 0) | 0; break;
        case 24: r = a & b; break;
        case 25: r = a | b; break;
        case 26: r = a ^ b; break;
        case 28: r = a << (b & 31); break;
        case 29: r = a >> (b & 31); break;
        case 30: r = a >>> (b & 31) | 0; break;
        case 32: r = a == b ? 1 : 0; break;
        case 33: r = a < b ? 1 : 0; break;
        default: r = (a >>> 0) < (b >>> 0) ? 1 : 0;
      }
      D[sp - 2] = r; sp--; continue;
    }
    switch (op) {
      case 0: return done(0);
      case 1: D[sp++] = (b1 << 24) >> 24; break;
      case 2: D[sp++] = b1 | b2 << 8 | p[pc - 2] << 16 | p[pc - 1] << 24; break;
      case 3: sp--; break;
      case 4: D[sp] = D[sp - 1]; sp++; break;
      case 5: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; }
      case 6: D[sp] = D[sp - 2]; sp++; break;
      case 7: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; }
      case 23: D[sp - 1] = -D[sp - 1] | 0; break;
      case 27: D[sp - 1] = ~D[sp - 1]; break;
      case 48: pc = nx + (((b1 | b2 << 8) << 16) >> 16); break;
      case 49: case 50: { const v = D[--sp], rel = ((b1 | b2 << 8) << 16) >> 16; if (op == 49 ? v == 0 : v != 0) pc = nx + rel; break; }
      case 51: if (cp >= 64) return done(7); C[cp++] = nx; pc = b1 | b2 << 8; break;
      case 52: if (cp == 0) return done(8); pc = C[--cp]; break;
      case 64: { const a = D[sp - 1]; if (a < 0 || a > 255) return done(6); D[sp - 1] = M[a]; break; }
      case 65: { const a = D[sp - 1]; if (a < 0 || a > 255) return done(6); M[a] = D[sp - 2]; sp -= 2; break; }
      case 80: { const s = String(D[--sp]); if (ol + s.length > 65536) return done(11); for (let i = 0; i < s.length; i++) O[ol++] = s.charCodeAt(i); break; }
      case 81: if (ol + 1 > 65536) return done(11); O[ol++] = D[--sp] & 255; break;
      case 82: D[sp++] = ip < inp.length ? inp[ip++] : -1; break;
      case 83: return done(D[--sp] & 255);
    }
  }
}
const IN = process.env.MAKEFUN_INPUT_DIR ?? '/input', OUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
mkdirSync(OUT, { recursive: true });
for (const id of readdirSync(IN).sort()) {
  const r = run(readFileSync(join(IN, id, 'program.bin')), readFileSync(join(IN, id, 'input.bin')));
  mkdirSync(join(OUT, id), { recursive: true });
  writeFileSync(join(OUT, id, 'stdout.bin'), r.out);
  writeFileSync(join(OUT, id, 'exit.txt'), r.code + '\n');
}
