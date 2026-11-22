// Tiny stack VM: runs every program of make.fun's tiny stack ISA (v1) in one run.
// Reads /input/<id>/program.bin + input.bin, writes /output/<id>/stdout.bin + exit.txt.
// Node 22, no dependencies, no clock, no network: fully deterministic.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

function run(p, inp) {
  const S = [], C = [], M = new Int32Array(256), out = [];
  let pc = 0, ip = 0, steps = 0;
  const trap = c => [out, c];
  for (;;) {
    if (steps >= 1000000) return trap(10);          // step limit
    if (pc < 0 || pc >= p.length) return trap(9);   // pc outside program
    const op = p[pc];
    const ok = op < 8 || (op >= 16 && op <= 30) || (op >= 32 && op <= 34)
      || (op >= 48 && op <= 52) || op === 64 || op === 65 || (op >= 80 && op <= 83);
    if (!ok) return trap(5);                        // unknown opcode
    let len = 1;
    if (op === 1) len = 2;
    else if (op >= 48 && op <= 51) len = 3;
    else if (op === 2) len = 5;
    if (pc + len > p.length) return trap(9);        // immediate cut off
    const nx = pc + len;
    steps++;
    // Stack needs first: underflow (2), then overflow (3).
    const need = (a, b) => S.length < a ? 2 : S.length - a + b > 256 ? 3 : 0;
    let t, a, b, v;
    switch (op) {
      case 0: return trap(0);                       // HALT
      case 1:                                       // PUSH8 (sign-extended)
        if (t = need(0, 1)) return trap(t);
        S.push((p[pc + 1] << 24) >> 24); pc = nx; break;
      case 2:                                       // PUSH32 (signed LE)
        if (t = need(0, 1)) return trap(t);
        S.push(p[pc + 1] | p[pc + 2] << 8 | p[pc + 3] << 16 | p[pc + 4] << 24);
        pc = nx; break;
      case 3: if (t = need(1, 0)) return trap(t); S.pop(); pc = nx; break; // POP
      case 4: if (t = need(1, 2)) return trap(t); S.push(S[S.length - 1]); pc = nx; break; // DUP
      case 5:                                       // SWAP
        if (t = need(2, 2)) return trap(t);
        b = S.pop(); a = S.pop(); S.push(b, a); pc = nx; break;
      case 6: if (t = need(2, 3)) return trap(t); S.push(S[S.length - 2]); pc = nx; break; // OVER
      case 7:                                       // ROT
        if (t = need(3, 3)) return trap(t);
        v = S.pop(); b = S.pop(); a = S.pop(); S.push(b, v, a); pc = nx; break;
      case 16: case 17: case 18: case 19: case 20: case 21: case 22:
      case 24: case 25: case 26: case 28: case 29: case 30:
      case 32: case 33: case 34:                     // binary arithmetic/logic/compare
        if (t = need(2, 1)) return trap(t);
        b = S.pop(); a = S.pop();
        if ((op === 19 || op === 20 || op === 21 || op === 22) && b === 0) return trap(4);
        if (op === 16) v = (a + b) | 0;
        else if (op === 17) v = (a - b) | 0;
        else if (op === 18) v = Math.imul(a, b);
        else if (op === 19) v = (a / b) | 0;
        else if (op === 20) v = (a % b) | 0;
        else if (op === 21) v = ((a >>> 0) / (b >>> 0)) | 0;
        else if (op === 22) v = ((a >>> 0) % (b >>> 0)) | 0;
        else if (op === 24) v = a & b;
        else if (op === 25) v = a | b;
        else if (op === 26) v = a ^ b;
        else if (op === 28) v = a << (b & 31);
        else if (op === 29) v = a >> (b & 31);
        else if (op === 30) v = (a >>> (b & 31)) | 0;
        else if (op === 32) v = a === b ? 1 : 0;
        else if (op === 33) v = a < b ? 1 : 0;
        else v = (a >>> 0) < (b >>> 0) ? 1 : 0;
        S.push(v); pc = nx; break;
      case 23: if (t = need(1, 1)) return trap(t); S.push((-S.pop()) | 0); pc = nx; break; // NEG
      case 27: if (t = need(1, 1)) return trap(t); S.push(~S.pop()); pc = nx; break; // NOT
      case 48: pc = nx + (((p[pc + 1] | p[pc + 2] << 8) << 16) >> 16); break; // JMP
      case 49: case 50:                         // JZ / JNZ
        if (t = need(1, 0)) return trap(t);
        v = S.pop();
        pc = (op === 49 ? v === 0 : v !== 0)
          ? nx + (((p[pc + 1] | p[pc + 2] << 8) << 16) >> 16) : nx;
        break;
      case 51:                                  // CALL
        if (C.length >= 64) return trap(7);
        C.push(nx); pc = p[pc + 1] | p[pc + 2] << 8; break;
      case 52:                                  // RET
        if (!C.length) return trap(8);
        pc = C.pop(); break;
      case 64:                                  // LOAD
        if (t = need(1, 1)) return trap(t);
        a = S.pop();
        if (a < 0 || a > 255) return trap(6);
        S.push(M[a]); pc = nx; break;
      case 65:                                  // STORE (v addr -- )
        if (t = need(2, 0)) return trap(t);
        a = S.pop(); v = S.pop();
        if (a < 0 || a > 255) return trap(6);
        M[a] = v; pc = nx; break;
      case 80: {                                // PRINT (decimal ASCII)
        if (t = need(1, 0)) return trap(t);
        const s = String(S.pop());
        if (out.length + s.length > 65536) return trap(11);
        for (let i = 0; i < s.length; i++) out.push(s.charCodeAt(i));
        pc = nx; break;
      }
      case 81:                                  // PUTC
        if (t = need(1, 0)) return trap(t);
        if (out.length + 1 > 65536) return trap(11);
        out.push(S.pop() & 255); pc = nx; break;
      case 82:                                  // IN
        if (t = need(0, 1)) return trap(t);
        S.push(ip < inp.length ? inp[ip++] : -1); pc = nx; break;
      case 83:                                  // EXIT
        if (t = need(1, 0)) return trap(t);
        return trap(S.pop() & 255);
    }
  }
}

for (const id of readdirSync(I).sort()) {
  const r = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), Buffer.from(r[0]));
  writeFileSync(join(O, id, 'exit.txt'), r[1] + '\n');
}
