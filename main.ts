// The World in One Day — Wednesday 25 November 2026.
// A code-drawn newspaper poster: six verified stories from the day's news,
// drawn pixel by pixel with a hand-made rasteriser, a 5x7 bitmap font and a
// hand-rolled PNG encoder. Node 22 standard library only, no network, no
// clock, no randomness: the same input always yields the same bytes.
// Writes entry.png into $MAKEFUN_OUTPUT_DIR (default /output).
import * as fs from "node:fs";
import * as path from "node:path";

const W = 1024;
const H = 1024;

// ---- colours ----
const PAPER = [245, 239, 221];
const PANEL = [251, 248, 239];
const TINT = [238, 229, 200];
const INK = [22, 22, 22];
const RED = [168, 35, 26];
const BLUE = [29, 78, 121];
const TEAL = [15, 107, 92];
const GOLD = [176, 124, 22];
const ORANGE = [214, 106, 24];
const GREY = [110, 108, 96];
const WHITE = [255, 255, 255];
const DARKBLUE = [18, 52, 84];

// ---- CRC32 + Adler32 (for the PNG encoder) ----
const CRC_TABLE: number[] = [];
for (let n = 0; n < 256; n++) {
  let c = n;
  for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
  CRC_TABLE[n] = c >>> 0;
}
function crc32(buf: Buffer): number {
  let c = 0xffffffff;
  for (let i = 0; i < buf.length; i++) c = CRC_TABLE[(c ^ buf[i]) & 0xff] ^ (c >>> 8);
  return (c ^ 0xffffffff) >>> 0;
}
function adler32(buf: Buffer): number {
  let a = 1;
  let b = 0;
  for (let i = 0; i < buf.length; i++) {
    a = (a + buf[i]) % 65521;
    b = (b + a) % 65521;
  }
  return ((b << 16) | a) >>> 0;
}
function chunk(type: string, data: Buffer): Buffer {
  const out = Buffer.alloc(12 + data.length);
  out.writeUInt32BE(data.length, 0);
  out.write(type, 4, "ascii");
  data.copy(out, 8);
  out.writeUInt32BE(crc32(Buffer.concat([Buffer.from(type, "ascii"), data])), 8 + data.length);
  return out;
}
// ---- DEFLATE with fixed Huffman codes (RFC 1951) ----
const LEN_BASE = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
const LEN_EXTRA = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
const DIST_BASE = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];
const DIST_EXTRA = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];
function lenCode(len: number): [number, number, number] {
  for (let i = LEN_BASE.length - 1; i >= 0; i--) {
    if (len >= LEN_BASE[i]) return [257 + i, LEN_EXTRA[i], len - LEN_BASE[i]];
  }
  return [257, 0, 0];
}
function distCode(d: number): [number, number, number] {
  for (let i = DIST_BASE.length - 1; i >= 0; i--) {
    if (d >= DIST_BASE[i]) return [i, DIST_EXTRA[i], d - DIST_BASE[i]];
  }
  return [0, 0, 0];
}
function litCode(sym: number): [number, number] {
  if (sym < 144) return [0x30 + sym, 8];
  if (sym < 256) return [0x190 + (sym - 144), 9];
  if (sym < 280) return [sym - 256, 7];
  return [0xc0 + (sym - 280), 8];
}
class BitWriter {
  bits: number[] = [];
  put(value: number, count: number): void {
    // Huffman codes go out most-significant bit first.
    for (let i = count - 1; i >= 0; i--) this.bits.push((value >> i) & 1);
  }
  putRaw(value: number, count: number): void {
    for (let i = 0; i < count; i++) this.bits.push((value >> i) & 1);
  }
  bytes(): Buffer {
    while (this.bits.length % 8) this.bits.push(0);
    const out = Buffer.alloc(this.bits.length / 8);
    for (let i = 0; i < this.bits.length; i++) {
      if (this.bits[i]) out[i >> 3] |= 1 << (i & 7);
    }
    return out;
  }
}
function deflateFixed(data: Buffer): Buffer {
  const w = new BitWriter();
  w.putRaw(1, 1); // BFINAL
  w.putRaw(1, 2); // BTYPE = 01 fixed Huffman
  const HASH_BITS = 15;
  const head = new Int32Array(1 << HASH_BITS).fill(-1);
  const prev = new Int32Array(data.length).fill(-1);
  const hashAt = (p: number): number =>
    (((data[p] << 10) ^ (data[p + 1] << 5) ^ data[p + 2]) & ((1 << HASH_BITS) - 1));
  let pos = 0;
  while (pos < data.length) {
    let bestLen = 0;
    let bestDist = 0;
    if (pos + 2 < data.length) {
      const h = hashAt(pos);
      let cand = head[h];
      let tries = 0;
      while (cand >= 0 && tries < 32 && pos - cand <= 32768) {
        let l = 0;
        while (
          l < 258 &&
          pos + l < data.length &&
          data[cand + l] === data[pos + l]
        )
          l++;
        if (l >= 3 && l > bestLen) {
          bestLen = l;
          bestDist = pos - cand;
          if (l >= 258) break;
        }
        cand = prev[cand];
        tries++;
      }
      prev[pos] = head[h];
      head[h] = pos;
    }
    if (bestLen >= 3) {
      const [lc, le, ev] = lenCode(bestLen);
      const [code, clen] = litCode(lc);
      w.put(code, clen);
      if (le) w.putRaw(ev, le);
      const [dc, de, dv] = distCode(bestDist);
      w.put(dc, 5);
      if (de) w.putRaw(dv, de);
      for (let k = 1; k < bestLen; k++) {
        const p = pos + k;
        if (p + 2 < data.length) {
          const h = hashAt(p);
          prev[p] = head[h];
          head[h] = p;
        }
      }
      pos += bestLen;
    } else {
      const [code, clen] = litCode(data[pos]);
      w.put(code, clen);
      pos++;
    }
  }
  const [ecode, elen] = litCode(256);
  w.put(ecode, elen);
  return w.bytes();
}
function pngEncode(rgb: Uint8Array, w: number, h: number): Buffer {
  const raw = Buffer.alloc(h * (1 + w * 3));
  for (let y = 0; y < h; y++) {
    raw[y * (1 + w * 3)] = 0;
    Buffer.from(rgb.buffer, y * w * 3, w * 3).copy(raw, y * (1 + w * 3) + 1);
  }
  const z = Buffer.concat([
    Buffer.from([0x78, 0x9c]),
    deflateFixed(raw),
    (() => {
      const t = Buffer.alloc(4);
      t.writeUInt32BE(adler32(raw), 0);
      return t;
    })(),
  ]);
  const ihdr = Buffer.alloc(13);
  ihdr.writeUInt32BE(w, 0);
  ihdr.writeUInt32BE(h, 4);
  ihdr[8] = 8; // bit depth
  ihdr[9] = 2; // colour type RGB
  ihdr[10] = 0;
  ihdr[11] = 0;
  ihdr[12] = 0;
  return Buffer.concat([
    Buffer.from([0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a]),
    chunk("IHDR", ihdr),
    chunk("IDAT", z),
    chunk("IEND", Buffer.alloc(0)),
  ]);
}

// ---- canvas ----
const px = new Uint8Array(W * H * 3);
function paint(c: number[]): void {
  for (let i = 0; i < W * H; i++) {
    px[i * 3] = c[0];
    px[i * 3 + 1] = c[1];
    px[i * 3 + 2] = c[2];
  }
}
function dot(x: number, y: number, c: number[]): void {
  if (x < 0 || y < 0 || x >= W || y >= H) return;
  const i = (y * W + x) * 3;
  px[i] = c[0];
  px[i + 1] = c[1];
  px[i + 2] = c[2];
}
function rect(x: number, y: number, w: number, h: number, c: number[]): void {
  for (let yy = y; yy < y + h; yy++)
    for (let xx = x; xx < x + w; xx++) dot(xx, yy, c);
}
function hline(x: number, y: number, w: number, c: number[]): void {
  for (let xx = x; xx < x + w; xx++) dot(xx, y, c);
}
function vline(x: number, y: number, h: number, c: number[]): void {
  for (let yy = y; yy < y + h; yy++) dot(x, yy, c);
}
function line(x0: number, y0: number, x1: number, y1: number, c: number[]): void {
  const dx = Math.abs(x1 - x0);
  const dy = -Math.abs(y1 - y0);
  const sx = x0 < x1 ? 1 : -1;
  const sy = y0 < y1 ? 1 : -1;
  let err = dx + dy;
  let x = x0;
  let y = y0;
  for (;;) {
    dot(x, y, c);
    if (x === x1 && y === y1) break;
    const e2 = 2 * err;
    if (e2 >= dy) {
      err += dy;
      x += sx;
    }
    if (e2 <= dx) {
      err += dx;
      y += sy;
    }
  }
}
function disc(cx: number, cy: number, r: number, c: number[]): void {
  for (let y = cy - r; y <= cy + r; y++) {
    const dy = y - cy;
    const hw = Math.floor(Math.sqrt(Math.max(0, r * r - dy * dy)));
    for (let x = cx - hw; x <= cx + hw; x++) dot(x, y, c);
  }
}
function ellipse(cx: number, cy: number, rx: number, ry: number, c: number[]): void {
  for (let y = cy - ry; y <= cy + ry; y++) {
    const t = (y - cy) / ry;
    const hw = Math.floor(rx * Math.sqrt(Math.max(0, 1 - t * t)));
    for (let x = cx - hw; x <= cx + hw; x++) dot(x, y, c);
  }
}
function tri(x0: number, y0: number, x1: number, y1: number, x2: number, y2: number, c: number[]): void {
  const minY = Math.min(y0, y1, y2);
  const maxY = Math.max(y0, y1, y2);
  for (let y = minY; y <= maxY; y++) {
    const xs: number[] = [];
    const edges: [number, number, number, number][] = [
      [x0, y0, x1, y1],
      [x1, y1, x2, y2],
      [x2, y2, x0, y0],
    ];
    for (const [ax, ay, bx, by] of edges) {
      if ((ay <= y && by > y) || (by <= y && ay > y)) {
        xs.push(ax + ((y - ay) / (by - ay)) * (bx - ax));
      }
    }
    if (xs.length >= 2) {
      const a = Math.ceil(Math.min(xs[0], xs[1]));
      const b = Math.floor(Math.max(xs[0], xs[1]));
      for (let x = a; x <= b; x++) dot(x, y, c);
    }
  }
}
function frame(x: number, y: number, w: number, h: number, c: number[], t: number): void {
  rect(x, y, w, t, c);
  rect(x, y + h - t, w, t, c);
  rect(x, y, t, h, c);
  rect(x + w - t, y, t, h, c);
}

// ---- 5x7 bitmap font (glyphs as 7 rows of 5 bits) ----
const GLYPHS: Record<string, number[]> = {
  A: [0b01110, 0b10001, 0b10001, 0b11111, 0b10001, 0b10001, 0b10001],
  B: [0b11110, 0b10001, 0b10001, 0b11110, 0b10001, 0b10001, 0b11110],
  C: [0b01110, 0b10001, 0b10000, 0b10000, 0b10000, 0b10001, 0b01110],
  D: [0b11110, 0b10001, 0b10001, 0b10001, 0b10001, 0b10001, 0b11110],
  E: [0b11111, 0b10000, 0b10000, 0b11110, 0b10000, 0b10000, 0b11111],
  F: [0b11111, 0b10000, 0b10000, 0b11110, 0b10000, 0b10000, 0b10000],
  G: [0b01110, 0b10001, 0b10000, 0b10111, 0b10001, 0b10001, 0b01111],
  H: [0b10001, 0b10001, 0b10001, 0b11111, 0b10001, 0b10001, 0b10001],
  I: [0b01110, 0b00100, 0b00100, 0b00100, 0b00100, 0b00100, 0b01110],
  J: [0b00111, 0b00010, 0b00010, 0b00010, 0b00010, 0b10010, 0b01100],
  K: [0b10001, 0b10010, 0b10100, 0b11000, 0b10100, 0b10010, 0b10001],
  L: [0b10000, 0b10000, 0b10000, 0b10000, 0b10000, 0b10000, 0b11111],
  M: [0b10001, 0b11011, 0b10101, 0b10101, 0b10001, 0b10001, 0b10001],
  N: [0b10001, 0b11001, 0b10101, 0b10011, 0b10001, 0b10001, 0b10001],
  O: [0b01110, 0b10001, 0b10001, 0b10001, 0b10001, 0b10001, 0b01110],
  P: [0b11110, 0b10001, 0b10001, 0b11110, 0b10000, 0b10000, 0b10000],
  Q: [0b01110, 0b10001, 0b10001, 0b10001, 0b10101, 0b10010, 0b01101],
  R: [0b11110, 0b10001, 0b10001, 0b11110, 0b10100, 0b10010, 0b10001],
  S: [0b01111, 0b10000, 0b10000, 0b01110, 0b00001, 0b00001, 0b11110],
  T: [0b11111, 0b00100, 0b00100, 0b00100, 0b00100, 0b00100, 0b00100],
  U: [0b10001, 0b10001, 0b10001, 0b10001, 0b10001, 0b10001, 0b01110],
  V: [0b10001, 0b10001, 0b10001, 0b10001, 0b10001, 0b01010, 0b00100],
  W: [0b10001, 0b10001, 0b10001, 0b10101, 0b10101, 0b11011, 0b10001],
  X: [0b10001, 0b10001, 0b01010, 0b00100, 0b01010, 0b10001, 0b10001],
  Y: [0b10001, 0b10001, 0b01010, 0b00100, 0b00100, 0b00100, 0b00100],
  Z: [0b11111, 0b00001, 0b00010, 0b00100, 0b01000, 0b10000, 0b11111],
  a: [0, 0, 0b01110, 0b00001, 0b01111, 0b10001, 0b01111],
  b: [0b10000, 0b10000, 0b11110, 0b10001, 0b10001, 0b10001, 0b11110],
  c: [0, 0, 0b01110, 0b10000, 0b10000, 0b10001, 0b01110],
  d: [0b00001, 0b00001, 0b01111, 0b10001, 0b10001, 0b10001, 0b01111],
  e: [0, 0, 0b01110, 0b10001, 0b11111, 0b10000, 0b01110],
  f: [0b00110, 0b01000, 0b01110, 0b01000, 0b01000, 0b01000, 0b01000],
  g: [0, 0, 0b01111, 0b10001, 0b10001, 0b01111, 0b00001],
  h: [0b10000, 0b10000, 0b11110, 0b10001, 0b10001, 0b10001, 0b10001],
  i: [0, 0b00100, 0, 0b01100, 0b00100, 0b00100, 0b01110],
  j: [0, 0b00010, 0, 0b00110, 0b00010, 0b00010, 0b01100],
  k: [0b10000, 0b10000, 0b10010, 0b10100, 0b11000, 0b10100, 0b10010],
  l: [0b01100, 0b00100, 0b00100, 0b00100, 0b00100, 0b00100, 0b01110],
  m: [0, 0, 0b11010, 0b10101, 0b10101, 0b10101, 0b10101],
  n: [0, 0, 0b11110, 0b10001, 0b10001, 0b10001, 0b10001],
  o: [0, 0, 0b01110, 0b10001, 0b10001, 0b10001, 0b01110],
  p: [0, 0, 0b11110, 0b10001, 0b10001, 0b11110, 0b10000],
  q: [0, 0, 0b01111, 0b10001, 0b10001, 0b01111, 0b00001],
  r: [0, 0, 0b10110, 0b11001, 0b10000, 0b10000, 0b10000],
  s: [0, 0, 0b01111, 0b10000, 0b01110, 0b00001, 0b11110],
  t: [0b01000, 0b01000, 0b01110, 0b01000, 0b01000, 0b01000, 0b00110],
  u: [0, 0, 0b10001, 0b10001, 0b10001, 0b10001, 0b01111],
  v: [0, 0, 0b10001, 0b10001, 0b10001, 0b01010, 0b00100],
  w: [0, 0, 0b10001, 0b10001, 0b10101, 0b10101, 0b01010],
  x: [0, 0, 0b10001, 0b01010, 0b00100, 0b01010, 0b10001],
  y: [0, 0, 0b10001, 0b10001, 0b10001, 0b01111, 0b00001],
  z: [0, 0, 0b11111, 0b00010, 0b00100, 0b01000, 0b11111],
  "0": [0b01110, 0b10001, 0b10011, 0b10101, 0b11001, 0b10001, 0b01110],
  "1": [0b00100, 0b01100, 0b00100, 0b00100, 0b00100, 0b00100, 0b01110],
  "2": [0b01110, 0b10001, 0b00001, 0b00110, 0b01000, 0b10000, 0b11111],
  "3": [0b11111, 0b00010, 0b00100, 0b00010, 0b00001, 0b10001, 0b01110],
  "4": [0b00010, 0b00110, 0b01010, 0b10010, 0b11111, 0b00010, 0b00010],
  "5": [0b11111, 0b10000, 0b11110, 0b00001, 0b00001, 0b10001, 0b01110],
  "6": [0b00110, 0b01000, 0b10000, 0b11110, 0b10001, 0b10001, 0b01110],
  "7": [0b11111, 0b00001, 0b00010, 0b00100, 0b01000, 0b01000, 0b01000],
  "8": [0b01110, 0b10001, 0b10001, 0b01110, 0b10001, 0b10001, 0b01110],
  "9": [0b01110, 0b10001, 0b10001, 0b01111, 0b00001, 0b00010, 0b01100],
  " ": [0, 0, 0, 0, 0, 0, 0],
  ".": [0, 0, 0, 0, 0, 0b01100, 0b01100],
  ",": [0, 0, 0, 0, 0, 0b01100, 0b01000],
  "'": [0b00100, 0b00100, 0b01000, 0, 0, 0, 0],
  "-": [0, 0, 0, 0b01110, 0, 0, 0],
  ":": [0, 0, 0b01100, 0, 0b01100, 0, 0],
  ";": [0, 0, 0b01100, 0, 0b01100, 0b00100, 0b01000],
  "!": [0b00100, 0b00100, 0b00100, 0b00100, 0b00100, 0, 0b00100],
  "?": [0b01110, 0b10001, 0b00001, 0b00010, 0b00100, 0, 0b00100],
  "%": [0b11001, 0b11010, 0b00010, 0b00100, 0b01000, 0b01011, 0b10011],
  $: [0b00100, 0b01111, 0b10100, 0b01110, 0b00101, 0b11110, 0b00100],
  "/": [0b00001, 0b00010, 0b00010, 0b00100, 0b01000, 0b01000, 0b10000],
  "(": [0b00010, 0b00100, 0b01000, 0b01000, 0b01000, 0b00100, 0b00010],
  ")": [0b01000, 0b00100, 0b00010, 0b00010, 0b00010, 0b00100, 0b01000],
  "&": [0b01100, 0b10010, 0b10100, 0b01000, 0b10101, 0b10010, 0b01101],
  "+": [0, 0, 0b00100, 0b01110, 0b00100, 0, 0],
  "=": [0, 0, 0b11111, 0, 0b11111, 0, 0],
  '"': [0b01010, 0b01010, 0, 0, 0, 0, 0],
  "#": [0b01010, 0b01010, 0b11111, 0b01010, 0b11111, 0b01010, 0b01010],
};

function glyph(ch: string): number[] {
  return GLYPHS[ch] ?? GLYPHS["?"];
}
function textW(s: string, scale: number): number {
  return s.length * 6 * scale - scale;
}
function drawGlyph(x: number, y: number, ch: string, scale: number, c: number[]): void {
  const g = glyph(ch);
  for (let r = 0; r < 7; r++) {
    for (let col = 0; col < 5; col++) {
      if (g[r] & (1 << (4 - col))) {
        rect(x + col * scale, y + r * scale, scale, scale, c);
      }
    }
  }
}
function drawText(x: number, y: number, s: string, scale: number, c: number[], bold = false): void {
  let cx = x;
  for (const ch of s) {
    drawGlyph(cx, y, ch, scale, c);
    if (bold) drawGlyph(cx + 1, y, ch, scale, c);
    cx += 6 * scale;
  }
}
function drawCentred(y: number, s: string, scale: number, c: number[], bold = false): void {
  drawText(Math.floor((W - textW(s, scale)) / 2), y, s, scale, c, bold);
}
function wrap(s: string, maxW: number, scale: number): string[] {
  const words = s.split(" ");
  const lines: string[] = [];
  let cur = "";
  for (const w of words) {
    const trial = cur ? cur + " " + w : w;
    if (textW(trial, scale) <= maxW || !cur) {
      cur = trial;
    } else {
      lines.push(cur);
      cur = w;
    }
  }
  if (cur) lines.push(cur);
  return lines;
}
function block(x: number, y: number, s: string, scale: number, maxW: number, c: number[], bold = false, lh?: number): number {
  const lines = wrap(s, maxW, scale);
  const step = lh ?? 7 * scale + 4;
  lines.forEach((ln, i) => drawText(x, y + i * step, ln, scale, c, bold));
  return y + lines.length * step;
}

// ---- small pictograms ----
function drawTankerScene(x: number, y: number, w: number, h: number): void {
  // sky, sun, sea, a tanker on fire
  rect(x, y, w, h, [214, 226, 232]);
  disc(x + w - 52, y + 34, 22, [232, 176, 60]);
  rect(x, y + Math.floor(h * 0.62), w, h - Math.floor(h * 0.62), [46, 96, 138]);
  for (let i = 0; i < 4; i++) {
    hline(x + 8 + i * 3, y + Math.floor(h * 0.62) + 12 + i * 14, w - 16 - i * 6, [120, 170, 205]);
  }
  // hull
  const hy = y + Math.floor(h * 0.42);
  rect(x + 18, hy, w - 36, 46, [30, 30, 30]);
  rect(x + 18, hy + 36, w - 36, 10, RED);
  // bridge tower
  rect(x + w - 78, hy - 34, 34, 34, [70, 70, 70]);
  rect(x + w - 72, hy - 28, 22, 8, [180, 210, 230]);
  // deck tanks
  for (let i = 0; i < 3; i++) rect(x + 34 + i * 52, hy - 14, 40, 14, [120, 118, 110]);
  // flames
  tri(x + 60, hy - 6, x + 76, hy - 52, x + 92, hy - 6, ORANGE);
  tri(x + 96, hy - 6, x + 110, hy - 40, x + 124, hy - 6, [232, 176, 60]);
  tri(x + 150, hy - 6, x + 164, hy - 46, x + 178, hy - 6, ORANGE);
  // smoke
  disc(x + 76, hy - 62, 10, [120, 118, 110]);
  disc(x + 92, hy - 76, 13, [140, 138, 130]);
  disc(x + 112, hy - 90, 10, [160, 158, 150]);
}
function drawPercentIcon(x: number, y: number, s: number, c: number[]): void {
  drawText(x, y, "%", s, c, true);
  rect(x, y + 7 * s + 6, 5 * s + 10, 4, c);
  rect(x, y + 7 * s + 14, 3 * s + 6, 4, c);
}
function drawChipIcon(x: number, y: number, s: number): void {
  const w = 9 * s;
  rect(x, y, w, w, [30, 30, 30]);
  rect(x + 2 * s, y + 2 * s, 5 * s, 5 * s, [180, 210, 230]);
  for (let i = 0; i < 3; i++) {
    rect(x + (2 + i * 3) * s, y - s, s, s, INK);
    rect(x + (2 + i * 3) * s, y + w, s, s, INK);
    rect(x - s, y + (2 + i * 3) * s, s, s, INK);
    rect(x + w, y + (2 + i * 3) * s, s, s, INK);
  }
}
function drawIslandsIcon(x: number, y: number, s: number): void {
  rect(x, y + 8 * s, 12 * s, 3 * s, [46, 96, 138]);
  rect(x, y + 11 * s, 12 * s, 2, [120, 170, 205]);
  ellipse(x + 3 * s, y + 4 * s, 3 * s, 2 * s, [46, 130, 80]);
  ellipse(x + 9 * s, y + 5 * s, 2 * s, 2 * s, [46, 130, 80]);
  disc(x + 3 * s, y + 1 * s, s, [232, 176, 60]);
}
function drawRocketIcon(x: number, y: number, s: number): void {
  rect(x + 4 * s, y + 3 * s, 4 * s, 6 * s, [240, 240, 240]);
  tri(x + 4 * s, y + 3 * s, x + 8 * s, y + 3 * s, x + 6 * s, y, RED);
  disc(x + 6 * s, y + 5 * s, s, BLUE);
  tri(x + 2 * s, y + 9 * s, x + 4 * s, y + 7 * s, x + 4 * s, y + 9 * s, RED);
  tri(x + 8 * s, y + 9 * s, x + 10 * s, y + 9 * s, x + 8 * s, y + 7 * s, RED);
  tri(x + 5 * s, y + 9 * s, x + 7 * s, y + 9 * s, x + 6 * s, y + 13 * s, ORANGE);
  line(x + 1 * s, y + 13 * s, x + 3 * s, y + 15 * s, GOLD);
  line(x + 3 * s, y + 13 * s, x + 1 * s, y + 15 * s, GOLD);
  line(x + 10 * s, y + 1 * s, x + 12 * s, y + 3 * s, GOLD);
  line(x + 12 * s, y + 1 * s, x + 10 * s, y + 3 * s, GOLD);
}
function drawBurstIcon(x: number, y: number, s: number): void {
  const cx = x + 6 * s;
  const cy = y + 6 * s;
  disc(cx, cy, 2 * s, RED);
  for (let i = 0; i < 8; i++) {
    const a = (i * Math.PI) / 4;
    const x1 = Math.round(cx + Math.cos(a) * 3 * s);
    const y1 = Math.round(cy + Math.sin(a) * 3 * s);
    const x2 = Math.round(cx + Math.cos(a) * 6 * s);
    const y2 = Math.round(cy + Math.sin(a) * 6 * s);
    line(x1, y1, x2, y2, ORANGE);
  }
}

// ---- the day's stories (verified against multiple news sources) ----
type Story = {
  tag: string;
  color: number[];
  headline: string;
  body: string;
  icon: (x: number, y: number, s: number) => void;
};
const LEAD: Story = {
  tag: "STRAIT OF HORMUZ",
  color: RED,
  headline: "Two tankers hit by mines in the Strait of Hormuz",
  body: "Iran's Revolutionary Guard said two oil tankers struck naval mines and caught fire while crossing the strait. Oil prices rose as shipping fears grew.",
  icon: drawTankerScene as never,
};
const STORIES: Story[] = [
  {
    tag: "TRADE",
    color: BLUE,
    headline: "US plans new tariffs on 14 economies",
    body: "Washington proposed tariffs of up to 20% on China, the EU, India and 11 others after a probe into industrial subsidies. Markets fell.",
    icon: (x, y, s) => drawPercentIcon(x, y, s, RED),
  },
  {
    tag: "TECH",
    color: TEAL,
    headline: "Huawei convicted in US fraud trial",
    body: "A Brooklyn jury found Huawei guilty on 10 of 12 counts, including bank fraud and conspiracy to steal trade secrets. It was cleared of racketeering.",
    icon: (x, y, s) => drawChipIcon(x, y, s),
  },
  {
    tag: "PACIFIC",
    color: TEAL,
    headline: "Australia signs Pacific security pact",
    body: "Australia and Solomon Islands signed a treaty in Canberra barring any foreign military or security base on the islands.",
    icon: (x, y, s) => drawIslandsIcon(x, y, s),
  },
  {
    tag: "SPACE",
    color: BLUE,
    headline: "First Pakistani reaches orbit",
    body: "China's Shenzhou-24 docked with Tiangong 3.5 hours after launch. Aboard was Pakistan's Muhammad Zeeshan Ali, the first foreign visitor to the station.",
    icon: (x, y, s) => drawRocketIcon(x, y, s),
  },
  {
    tag: "SUDAN",
    color: RED,
    headline: "Drone strikes kill 19 civilians in Sudan",
    body: "Emergency Lawyers said paramilitary RSF drones killed 19 people and wounded 20 in two cities in Blue Nile state.",
    icon: (x, y, s) => drawBurstIcon(x, y, s),
  },
];

function drawStoryPanel(x: number, y: number, w: number, h: number, st: Story, bg: number[]): void {
  rect(x, y, w, h, bg);
  frame(x, y, w, h, INK, 2);
  rect(x, y, w, 6, st.color);
  const pad = 14;
  drawText(x + pad, y + 18, st.tag, 2, st.color, true);
  const headY = block(x + pad, y + 46, st.headline, 2, w - pad * 2, INK, true, 22);
  block(x + pad, headY + 8, st.body, 2, w - pad * 2, INK, false, 18);
  // pictogram in the empty bottom-right corner, clear of the text
  st.icon(x + w - pad - 52, y + h - 64, 4);
}

function drawPoster(): void {
  paint(PAPER);
  // masthead
  drawCentred(30, "THE WORLD IN ONE DAY", 5, INK, true);
  hline(24, 96, 976, INK);
  hline(24, 100, 976, INK);
  drawCentred(112, "WEDNESDAY, 25 NOVEMBER 2026", 3, RED, true);
  drawCentred(146, "Six stories from around the world, as reported today", 2, INK);
  // lead story
  const LX = 24;
  const LY = 176;
  const LW = 976;
  const LH = 214;
  rect(LX, LY, LW, LH, PANEL);
  frame(LX, LY, LW, LH, INK, 2);
  rect(LX, LY, LW, 6, RED);
  drawText(LX + 18, LY + 20, LEAD.tag + "  -  LEAD STORY", 2, RED, true);
  block(LX + 18, LY + 50, LEAD.headline, 3, 560, INK, true, 26);
  block(LX + 18, LY + 118, LEAD.body, 2, 560, INK, false, 18);
  drawTankerScene(LX + 612, LY + 44, 330, 150);
  // grid row A: three panels
  const rowA = 404;
  const rowH = 282;
  const cols = [24, 356, 688];
  for (let i = 0; i < 3; i++) {
    drawStoryPanel(cols[i], rowA, 312, rowH, STORIES[i], i % 2 ? TINT : PANEL);
  }
  // grid row B: two wide panels
  const rowB = 700;
  drawStoryPanel(24, rowB, 478, rowH, STORIES[3], PANEL);
  drawStoryPanel(522, rowB, 478, rowH, STORIES[4], TINT);
  // footer
  hline(24, 992, 976, INK);
  drawCentred(1000, "Drawn in code. Sources: AP, Reuters, Xinhua, Just Security.", 1, GREY);
}

function main(): void {
  drawPoster();
  const outDir = process.env.MAKEFUN_OUTPUT_DIR || "/output";
  fs.mkdirSync(outDir, { recursive: true });
  const png = pngEncode(px, W, H);
  fs.writeFileSync(path.join(outDir, "entry.png"), png);
}

main();
