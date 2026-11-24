// Tiny stack VM for make.fun's tiny-stack-vm-01 (ISA v1): 32-bit wrapping
// ints, 256-value stack, 64-deep call stack, 256 words of memory, ten traps.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
// Opcode rows [byte, immediate bytes, pops, pushes] from the ISA table.
// The binary ops share one shape (pops 2, pushes 1) except NEG/NOT (1, 1).
const S = [[0,0,0,0],[1,1,0,1],[2,4,0,1],[3,0,1,0],[4,0,1,2],[5,0,2,2],[6,0,2,3],[7,0,3,3]];
for (const b of [16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,32,33,34]) S.push([b,0,b===23||b===27?1:2,1]);
S.push([48,2,0,0],[49,2,1,0],[50,2,1,0],[51,2,0,0],[52,0,0,0],[64,0,1,1],[65,0,2,0],[80,0,1,0],[81,0,1,0],[82,0,0,1],[83,0,1,0]);
// One packed byte per opcode: bit 7 set when known, then imm, pops, pushes.
const T = new Uint8Array(256);
for (const [b, i, p, q] of S) T[b] = 128 | (i << 4) | (p << 2) | q;

function run(g: Uint8Array, inp: Uint8Array) {
  const m = g.length;
  const D = new Int32Array(256);
  let s = 0;
  const C = new Int32Array(64);
  let d = 0;
  const M = new Int32Array(256);
  const O = new Uint8Array(65536);
  let l = 0;
  let q = 0;
  let p = 0;
  let t = 0;
  const e = (c: number) => ({ o: O.slice(0, l), c });
  for (;;) {
    if (t === 1e6) return e(10);
    if (p < 0 || p >= m) return e(9);
    const a = g[p];
    const tb = T[a];
    if (!tb) return e(5);
    const v = (tb >> 4) & 7;
    if (p + v >= m) return e(9);
    t++;
    const x = p + 1 + v;
    const y = (tb >> 2) & 3;
    const z = tb & 3;
    if (s < y) return e(2);
    if (s - y + z > 256) return e(3);
    p = x;
    switch (a) {
      case 0:
        return e(0);
      case 1:
        D[s++] = (g[x - 1] << 24) >> 24; // PUSH8, sign-extended
        break;
      case 2:
        D[s++] = g[x - 4] | (g[x - 3] << 8) | (g[x - 2] << 16) | (g[x - 1] << 24);
        break;
      case 3:
        s--;
        break;
      case 4:
        D[s] = D[s - 1];
        s++;
        break;
      case 5: {
        const w = D[s - 1];
        D[s - 1] = D[s - 2];
        D[s - 2] = w;
        break;
      }
      case 6:
        D[s] = D[s - 2];
        s++;
        break;
      case 7: {
        const w = D[s - 3];
        D[s - 3] = D[s - 2];
        D[s - 2] = D[s - 1];
        D[s - 1] = w;
        break;
      }
      case 16: case 17: case 18: case 19: case 20: case 21: case 22:
      case 24: case 25: case 26: case 28: case 29: case 30:
      case 32: case 33: case 34: {
        const b = D[s - 1];
        const f = D[s - 2];
        let r: number;
        if (a === 16) r = (f + b) | 0;
        else if (a === 17) r = (f - b) | 0;
        else if (a === 18) r = Math.imul(f, b);
        else if (a === 19) {
          if (!b) return e(4);
          r = f === -2147483648 && b === -1 ? f : (f / b) | 0;
        } else if (a === 20) {
          if (!b) return e(4);
          r = b === -1 ? 0 : (f % b) | 0; // MOD: sign of f, x % -1 is 0
        } else if (a === 21) {
          if (!b) return e(4);
          r = Math.floor((f >>> 0) / (b >>> 0)) | 0; // DIVU: unsigned
        } else if (a === 22) {
          if (!b) return e(4);
          r = ((f >>> 0) % (b >>> 0)) | 0; // MODU: unsigned
        } else if (a === 24) r = f & b;
        else if (a === 25) r = f | b;
        else if (a === 26) r = f ^ b;
        else if (a === 28) r = f << (b & 31);
        else if (a === 29) r = f >> (b & 31);
        else if (a === 30) r = (f >>> (b & 31)) | 0;
        else if (a === 32) r = f === b ? 1 : 0;
        else if (a === 33) r = f < b ? 1 : 0;
        else r = (f >>> 0) < (b >>> 0) ? 1 : 0; // LTU: unsigned
        s -= 2;
        D[s++] = r;
        break;
      }
      case 23:
        D[s - 1] = (-D[s - 1]) | 0;
        break;
      case 27:
        D[s - 1] = ~D[s - 1];
        break;
      case 48: case 49: case 50: {
        const w = ((g[x - 2] | (g[x - 1] << 8)) << 16) >> 16;
        if (a === 48) p = x + w;
        else {
          const u = D[--s];
          if ((a === 49) === (u === 0)) p = x + w;
        }
        break;
      }
      case 51:
        if (d === 64) return e(7);
        C[d++] = x;
        p = g[x - 2] | (g[x - 1] << 8);
        break;
      case 52:
        if (!d) return e(8);
        p = C[--d];
        break;
      case 64: {
        const w = D[s - 1];
        if (w < 0 || w >= 256) return e(6);
        D[s - 1] = M[w];
        break;
      }
      case 65: {
        const w = D[s - 1];
        if (w < 0 || w >= 256) return e(6);
        M[w] = D[s - 2];
        s -= 2;
        break;
      }
      case 80: {
        const w = String(D[s - 1]);
        if (l + w.length > 65536) return e(11);
        for (let i = 0; i < w.length; i++) O[l++] = w.charCodeAt(i);
        s--;
        break;
      }
      case 81:
        if (l + 1 > 65536) return e(11);
        O[l++] = D[--s] & 255;
        break;
      case 82:
        D[s++] = q < inp.length ? inp[q++] : -1;
        break;
      case 83:
        return e(D[--s] & 255);
    }
  }
}

const A = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const B = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(A).sort()) {
  const g = new Uint8Array(readFileSync(join(A, id, 'program.bin')));
  let inp: Buffer;
  try {
    inp = readFileSync(join(A, id, 'input.bin'));
  } catch {
    inp = Buffer.alloc(0);
  }
  const { o, c } = run(g, new Uint8Array(inp));
  mkdirSync(join(B, id), { recursive: true });
  writeFileSync(join(B, id, 'stdout.bin'), o);
  writeFileSync(join(B, id, 'exit.txt'), `${c}\n`);
}
