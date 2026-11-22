import * as fs from 'node:fs';
import * as path from 'node:path';

const OP = new Uint16Array(256);
const def = (o: number, i: number, p: number, u: number) => { OP[o] = 0x8000 | (i << 8) | (p << 4) | u; };
[0, 52].forEach(o => def(o, 0, 0, 0));
def(1, 1, 0, 1); def(2, 4, 0, 1); def(3, 0, 1, 0); def(4, 0, 1, 2);
def(5, 0, 2, 2); def(6, 0, 2, 3); def(7, 0, 3, 3);
[16,17,18,19,20,21,22,24,25,26,28,29,30,32,33,34].forEach(o => def(o, 0, 2, 1));
[23, 27, 64].forEach(o => def(o, 0, 1, 1));
def(48, 2, 0, 0); def(49, 2, 1, 0); def(50, 2, 1, 0); def(51, 2, 0, 0);
def(65, 0, 2, 0); def(80, 0, 1, 0); def(81, 0, 1, 0); def(82, 0, 0, 1); def(83, 0, 1, 0);

function runVM(prog: Uint8Array, input: Uint8Array): { exitCode: number; stdout: Uint8Array } {
  const progLen = prog.length, inLen = input.length;
  let pc = 0, steps = 0, sp = 0, csp = 0, outp = 0, inp = 0;
  const stack = new Int32Array(256), callStack = new Int32Array(64), memory = new Int32Array(256), outBuf = new Uint8Array(65536);
  const ret = (code: number) => ({ exitCode: code, stdout: outBuf.subarray(0, outp) });
  const jmpOff = (p: number) => (p + 3) + (((prog[p + 1] | (prog[p + 2] << 8)) << 16) >> 16);

  while (true) {
    if (steps >= 1000000) return ret(10);
    if (pc < 0 || pc >= progLen) return ret(9);
    const op = prog[pc];
    const info = OP[op];
    if ((info & 0x8000) === 0) return ret(5);
    const immLen = (info >> 8) & 15;
    if (pc + 1 + immLen > progLen) return ret(9);
    steps++;

    const pops = (info >> 4) & 15, pushes = info & 15;
    if (sp < pops) return ret(2);
    if (sp - pops + pushes > 256) return ret(3);

    if (op === 0x00) return ret(0);
    if (op === 0x01) { stack[sp++] = (prog[pc + 1] << 24) >> 24; pc += 2; continue; }
    if (op === 0x02) { stack[sp++] = prog[pc + 1] | (prog[pc + 2] << 8) | (prog[pc + 3] << 16) | (prog[pc + 4] << 24); pc += 5; continue; }
    if (op === 0x03) { sp--; pc++; continue; }
    if (op === 0x04) { stack[sp] = stack[sp - 1]; sp++; pc++; continue; }
    if (op === 0x05) { const t = stack[sp - 1]; stack[sp - 1] = stack[sp - 2]; stack[sp - 2] = t; pc++; continue; }
    if (op === 0x06) { stack[sp] = stack[sp - 2]; sp++; pc++; continue; }
    if (op === 0x07) { const a = stack[sp - 3]; stack[sp - 3] = stack[sp - 2]; stack[sp - 2] = stack[sp - 1]; stack[sp - 1] = a; pc++; continue; }

    if (op >= 0x10 && op <= 0x22 && op !== 0x17 && op !== 0x1b) {
      const b = stack[sp - 1], a = stack[sp - 2];
      let r = 0;
      if (op === 0x10) r = (a + b) | 0;
      else if (op === 0x11) r = (a - b) | 0;
      else if (op === 0x12) r = Math.imul(a, b);
      else if (op === 0x13) { if (b === 0) return ret(4); r = (a === -2147483648 && b === -1) ? -2147483648 : ((a / b) | 0); }
      else if (op === 0x14) { if (b === 0) return ret(4); r = (b === -1) ? 0 : ((a % b) | 0); }
      else if (op === 0x15) { const ub = b >>> 0; if (ub === 0) return ret(4); r = Math.floor((a >>> 0) / ub) | 0; }
      else if (op === 0x16) { const ub = b >>> 0; if (ub === 0) return ret(4); r = ((a >>> 0) % ub) | 0; }
      else if (op === 0x18) r = a & b;
      else if (op === 0x19) r = a | b;
      else if (op === 0x1a) r = a ^ b;
      else if (op === 0x1c) r = a << (b & 31);
      else if (op === 0x1d) r = a >> (b & 31);
      else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
      else if (op === 0x20) r = a === b ? 1 : 0;
      else if (op === 0x21) r = a < b ? 1 : 0;
      else if (op === 0x22) r = (a >>> 0) < (b >>> 0) ? 1 : 0;
      stack[sp - 2] = r; sp--; pc++; continue;
    }

    if (op === 0x17) { stack[sp - 1] = (-stack[sp - 1]) | 0; pc++; continue; }
    if (op === 0x1b) { stack[sp - 1] = ~stack[sp - 1]; pc++; continue; }

    if (op === 0x30) { pc = jmpOff(pc); continue; }
    if (op === 0x31) { pc = (stack[--sp] === 0) ? jmpOff(pc) : pc + 3; continue; }
    if (op === 0x32) { pc = (stack[--sp] !== 0) ? jmpOff(pc) : pc + 3; continue; }
    if (op === 0x33) {
      if (csp >= 64) return ret(7);
      callStack[csp++] = pc + 3;
      pc = prog[pc + 1] | (prog[pc + 2] << 8);
      continue;
    }
    if (op === 0x34) {
      if (csp === 0) return ret(8);
      pc = callStack[--csp];
      continue;
    }

    if (op === 0x40) {
      const addr = stack[sp - 1];
      if (addr < 0 || addr > 255) return ret(6);
      stack[sp - 1] = memory[addr];
      pc++;
      continue;
    }
    if (op === 0x41) {
      const addr = stack[--sp], val = stack[--sp];
      if (addr < 0 || addr > 255) return ret(6);
      memory[addr] = val;
      pc++;
      continue;
    }

    if (op === 0x50) {
      const s = String(stack[--sp]), slen = s.length;
      if (outp + slen > 65536) return ret(11);
      for (let i = 0; i < slen; i++) outBuf[outp++] = s.charCodeAt(i);
      pc++;
      continue;
    }
    if (op === 0x51) {
      if (outp + 1 > 65536) return ret(11);
      outBuf[outp++] = stack[--sp] & 255;
      pc++;
      continue;
    }
    if (op === 0x52) { stack[sp++] = (inp < inLen) ? input[inp++] : -1; pc++; continue; }
    if (op === 0x53) return { exitCode: stack[--sp] & 255, stdout: outBuf.subarray(0, outp) };
  }
}

function main() {
  const inDir = process.env.MAKEFUN_INPUT_DIR || '/input';
  const outDir = process.env.MAKEFUN_OUTPUT_DIR || '/output';
  if (!fs.existsSync(inDir)) return;

  const ids = fs.readdirSync(inDir).filter(f => fs.existsSync(path.join(inDir, f, 'program.bin'))).sort();
  for (const id of ids) {
    const dir = path.join(inDir, id);
    const prog = fs.readFileSync(path.join(dir, 'program.bin'));
    const inPath = path.join(dir, 'input.bin');
    const input = fs.existsSync(inPath) ? fs.readFileSync(inPath) : new Uint8Array(0);
    const res = runVM(prog, input);
    const targetDir = path.join(outDir, id);
    fs.mkdirSync(targetDir, { recursive: true });
    fs.writeFileSync(path.join(targetDir, 'stdout.bin'), res.stdout);
    fs.writeFileSync(path.join(targetDir, 'exit.txt'), `${res.exitCode}\n`);
  }
}

main();
