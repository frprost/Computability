/* turing.js — Turing machine simulator and compiler
   "recursive functions -> Turing machines" for the computability manual.
   Runs in the browser (window.Turing) and under Node (module.exports).

   Conventions (those of the chapter "Turing machines"):
   - quadruple machine (q, s, a, q') where a is a symbol (write), L or R;
   - an integer x is coded by x+1 strokes "1"; arguments are separated by a blank B;
   - the machine starts in state q0, the head on the first stroke of the first argument;
   - the result is the total number of strokes on the tape when it halts.
*/
(function (root) {
  'use strict';

  /* ------------------------------------------------------------------ */
  /* Reading a program text                                            */
  /* ------------------------------------------------------------------ */
  // Accepted format: one quadruple per line or separated by ";"
  //   q0 1 B q1      or   (q0, 1, B, q1)
  function parseQuads(text) {
    var quads = [];
    text.split(/[;\n]/).forEach(function (line) {
      line = line.replace(/#.*$/, '').replace(/[(),]/g, ' ').trim();
      if (!line) return;
      var p = line.split(/\s+/);
      if (p.length !== 4) throw new Error('Malformed quadruple: "' + line + '"');
      quads.forEach(function (q) {
        if (q[0] === p[0] && q[1] === p[1] && (q[2] !== p[2] || q[3] !== p[3]))
          throw new Error('Inconsistent machine: two quadruples start with "' + p[0] + ' ' + p[1] + '"');
      });
      quads.push(p);
    });
    return quads;
  }
  function parseQuints(text) {
    var qs = [];
    text.split(/[;\n]/).forEach(function (line) {
      line = line.replace(/#.*$/, '').replace(/[(),]/g, ' ').trim();
      if (!line) return;
      var p = line.split(/\s+/);
      if (p.length !== 5) throw new Error('Malformed quintuple: "' + line + '"');
      qs.forEach(function (q) {
        if (q[0] === p[0] && q[1] === p[1] && q.join(' ') !== p.join(' '))
          throw new Error('Inconsistent machine: two quintuples start with "' + p[0] + ' ' + p[1] + '"');
      });
      qs.push(p);
    });
    return qs;
  }

  /* ------------------------------------------------------------------ */
  /* Quadruple machine                                                  */
  /* ------------------------------------------------------------------ */
  function QuadMachine(quads) {
    this.quads = quads;
    this.table = Object.create(null);
    for (var i = 0; i < quads.length; i++) {
      var k = quads[i][0] + '\u0000' + quads[i][1];
      if (this.table[k]) throw new Error('Inconsistent machine: two quadruples start with ' + quads[i][0] + ', ' + quads[i][1]);
      this.table[k] = quads[i];
    }
  }
  // Initial tape for a tuple of integers
  function encodeArgs(args) {
    var cells = [];
    args.forEach(function (x, j) {
      if (j > 0) cells.push('B');
      for (var t = 0; t <= x; t++) cells.push('1');
    });
    return cells;
  }
  QuadMachine.prototype.start = function (args, initialState) {
    var tape = new Map();
    encodeArgs(args).forEach(function (s, i) { if (s !== 'B') tape.set(i, s); });
    return { tape: tape, pos: 0, state: initialState || 'q0', steps: 0, halted: false };
  };
  QuadMachine.prototype.step = function (c) {
    var s = c.tape.get(c.pos) || 'B';
    var q = this.table[c.state + '\u0000' + s];
    if (!q) { c.halted = true; return false; }
    var a = q[2];
    if (a === 'L') c.pos--;
    else if (a === 'R') c.pos++;
    else if (a === 'B') c.tape.delete(c.pos);
    else c.tape.set(c.pos, a);
    c.state = q[3];
    c.steps++;
    return true;
  };
  QuadMachine.prototype.run = function (args, maxSteps) {
    var c = this.start(args);
    maxSteps = maxSteps || 1e7;
    while (c.steps < maxSteps && this.step(c)) {}
    return c;
  };
  function countOnes(c) {
    var n = 0;
    c.tape.forEach(function (v) { if (v === '1') n++; });
    return n;
  }
  // Instantaneous description (word γ q S δ), useless blanks removed
  function describe(c) {
    var keys = Array.from(c.tape.keys());
    var lo = Math.min.apply(null, keys.concat([c.pos]));
    var hi = Math.max.apply(null, keys.concat([c.pos]));
    var out = [];
    for (var i = lo; i <= hi; i++) {
      if (i === c.pos) out.push('[' + c.state + ']');
      out.push(c.tape.get(i) || 'B');
    }
    return out.join(' ');
  }

  /* ------------------------------------------------------------------ */
  /* Rado machines (quintuples, symbols B and 1, halting state h)      */
  /* Fast array-based execution, used for the busy beavers.            */
  /* ------------------------------------------------------------------ */
  function runRado(quints, maxSteps, onProgress) {
    var states = {}, ns = 0;
    function sid(q) { if (q === 'h' || q === 'H') return -1; if (!(q in states)) states[q] = ns++; return states[q]; }
    var first = quints[0][0];
    sid(first);
    var W = [], M = [], N = [];
    quints.forEach(function (t) {
      var q = sid(t[0]), s = (t[1] === '1' || t[1] === '|') ? 1 : 0;
      var idx = q * 2 + s;
      W[idx] = (t[2] === '1' || t[2] === '|') ? 1 : 0;
      M[idx] = (t[3] === 'R' || t[3] === 'D') ? 1 : -1;
      N[idx] = sid(t[4]);
    });
    var size = 1 << 16, tape = new Uint8Array(size), pos = size >> 1, q = 0, steps = 0, lo = pos, hi = pos;
    maxSteps = maxSteps || 1e8;
    while (q >= 0 && steps < maxSteps) {
      var idx = q * 2 + tape[pos];
      if (W[idx] === undefined) break;
      tape[pos] = W[idx];
      pos += M[idx];
      q = N[idx];
      steps++;
      if (pos < 0 || pos >= size) { // grow the tape
        var nt = new Uint8Array(size * 2); nt.set(tape, size >> 1);
        pos += size >> 1; lo += size >> 1; hi += size >> 1; tape = nt; size *= 2;
      }
      if (pos < lo) lo = pos; if (pos > hi) hi = pos;
    }
    var ones = 0;
    for (var i = 0; i < size; i++) ones += tape[i];
    return { steps: steps, ones: ones, halted: q < 0, tape: tape, lo: lo, hi: hi, pos: pos };
  }

  /* ------------------------------------------------------------------ */
  /* Compiler: recursive functions -> quadruple machine                */
  /* ------------------------------------------------------------------ */
  // Terms:
  //   {t:'const', k, m}     (x1..xk) |-> m
  //   {t:'succ'}            x |-> x+1
  //   {t:'proj', k, i}      (x1..xk) |-> xi
  //   {t:'comp', g, hs:[...]}  sigma[g, h1..hk]   (arity = arity of the hi)
  //   {t:'rec', g, h}       rho[g, h]   f(0,x)=g(x), f(y+1,x)=h(y, f(y,x), x)
  //   {t:'mu', g}           mu[g](x) = least y such that g(x, y) = 0
  function arity(f) {
    switch (f.t) {
      case 'const': return f.k;
      case 'succ': return 1;
      case 'proj': return f.k;
      case 'comp': return arity(f.hs[0]);
      case 'rec': return arity(f.g) + 1;
      case 'mu': return arity(f.g) - 1;
    }
    throw new Error('unknown term ' + f.t);
  }
  function evalTerm(f, args, fuel) {
    fuel = fuel || { n: 1e6 };
    if (--fuel.n < 0) throw new Error('fuel');
    switch (f.t) {
      case 'const': return f.m;
      case 'succ': return args[0] + 1;
      case 'proj': return args[f.i - 1];
      case 'comp': return evalTerm(f.g, f.hs.map(function (h) { return evalTerm(h, args, fuel); }), fuel);
      case 'rec': {
        var y = args[0], rest = args.slice(1), acc = evalTerm(f.g, rest, fuel);
        for (var i = 0; i < y; i++) acc = evalTerm(f.h, [i, acc].concat(rest), fuel);
        return acc;
      }
      case 'mu': {
        for (var z = 0; ; z++) { if (evalTerm(f.g, args.concat([z]), fuel) === 0) return z; }
      }
    }
  }
  // Readable printing of a term
  function show(f) {
    switch (f.t) {
      case 'const': return f.m + '^{(' + f.k + ')}';
      case 'succ': return 'S';
      case 'proj': return 'A^{(' + f.k + ')}_{' + f.i + '}';
      case 'comp': return '\\sigma[' + [f.g].concat(f.hs).map(show).join(', ') + ']';
      case 'rec': return '\\rho[' + show(f.g) + ', ' + show(f.h) + ']';
      case 'mu': return '\\mu[' + show(f.g) + ']';
    }
  }

  function Builder() { this.n = 1; this.quads = []; }
  Builder.prototype.fresh = function () { return this.n++; };
  Builder.prototype.q = function (a, s, act, b) { this.quads.push([a, s, act, b]); };
  var SYMS = ['B', '1', 'X'];
  // State change with no effect (read then rewrite the same symbol)
  Builder.prototype.link = function (a, b) { var self = this; SYMS.forEach(function (s) { self.q(a, s, s, b); }); };

  // Invariant: the tape contains blocks of "1" separated by a single B.
  // E denotes the cell two cells after the last stroke (where a new block would start).

  // Go to E from any cell of the content (stroke, X or separator)
  Builder.prototype.gotoEnd = function (e) {
    var a = e, b = this.fresh(), x = this.fresh();
    this.q(a, '1', 'R', a); this.q(a, 'X', 'R', a); this.q(a, 'B', 'R', b);
    this.q(b, '1', 'R', a); this.q(b, 'X', 'R', a); this.q(b, 'B', 'B', x);
    return x;
  };
  // From E, go to the first cell of the j-th block counting from the end
  Builder.prototype.gotoBlock = function (e, j) {
    var s1 = this.fresh();
    this.q(e, 'B', 'L', s1);           // on the separator after the last block
    var cur = s1;
    for (var t = 1; t <= j; t++) {
      var scan = this.fresh();
      this.q(cur, 'B', 'L', scan);     // on the last cell of the current block
      this.q(scan, '1', 'L', scan);
      if (t < j) { var nx = this.fresh(); this.q(scan, 'B', 'B', nx); cur = nx; }
      else { var done = this.fresh(); this.q(scan, 'B', 'R', done); return done; }
    }
  };
  // Append a block coding m
  Builder.prototype.append = function (e, m) {
    var cur = e;
    for (var t = 0; t <= m; t++) {
      var w = this.fresh(), nx = this.fresh();
      this.q(cur, 'B', '1', w); this.q(w, '1', 'R', nx); cur = nx;
    }
    var x = this.fresh(); this.q(cur, 'B', 'R', x); return x;
  };
  // Copy the j-th block (from the end) to the end of the tape
  Builder.prototype.copy = function (e, j) {
    var s = this.gotoBlock(e, j);
    // first stroke
    var c1 = this.fresh(); this.q(s, '1', 'X', c1);
    var e1 = this.gotoEnd(c1);
    var r0 = this.fresh(); this.q(e1, 'B', '1', r0);
    // back to X
    this.q(r0, '1', 'L', r0); this.q(r0, 'B', 'L', r0);
    var r1 = this.fresh(); this.q(r0, 'X', '1', r1);
    var r2 = this.fresh(); this.q(r1, '1', 'R', r2);
    // following strokes
    var d1 = this.fresh(); this.q(r2, '1', 'X', d1);
    var e2 = this.gotoEnd(d1);
    var e3 = this.fresh(); this.q(e2, 'B', 'L', e3); this.q(e3, 'B', '1', r0);
    // end of the source
    var f0 = this.fresh(); this.q(r2, 'B', 'B', f0);
    return this.gotoEnd(f0);
  };
  // Shift the last k blocks one cell to the left.
  // Start on a blank cell g, g+1 blank, g+2 start of a block. End at E.
  Builder.prototype.shiftTail = function (g, k) {
    var cur = g;
    for (var t = 0; t < k; t++) {
      var a = this.fresh(), b = this.fresh(), c = this.fresh(), d = this.fresh();
      this.q(cur, 'B', 'R', a); this.q(a, 'B', '1', b);
      this.q(b, '1', 'R', b); this.q(b, 'B', 'L', c);
      this.q(c, '1', 'B', d); cur = d;
    }
    var x = this.fresh(); this.q(cur, 'B', 'R', x); return x;
  };
  // Remove a stroke from the j-th block (assumed to code an integer > 0)
  Builder.prototype.dec = function (e, j) {
    var s = this.gotoBlock(e, j);
    var p = this.fresh(); this.link(s, p);
    this.q(p, '1', 'R', p); var p2 = this.fresh(); this.q(p, 'B', 'L', p2);
    var z = this.fresh(); this.q(p2, '1', 'B', z);
    return this.shiftTail(z, j - 1);
  };
  // Delete the j-th block from the end entirely
  Builder.prototype.del = function (e, j) {
    var loop = e;
    var s = this.gotoBlock(loop, j);
    var p = this.fresh(); this.link(s, p);
    this.q(p, '1', 'R', p); var p2 = this.fresh(); this.q(p, 'B', 'L', p2);
    var z = this.fresh(); this.q(p2, '1', 'B', z);
    var p4 = this.fresh(); this.q(z, 'B', 'L', p4);
    // nonempty block: go back to z, shift the tail, start again
    var z2 = this.fresh(); this.q(p4, '1', 'R', z2);
    var back = this.shiftTail(z2, j - 1);
    this.link(back, loop);
    // empty block: we are on the left separator w
    var w = this.fresh(); this.q(p4, 'B', 'B', w);
    if (j === 1) { var x = this.fresh(); this.q(w, 'B', 'R', x); return x; }
    var z3 = this.fresh(); this.q(w, 'B', 'R', z3);
    var e1 = this.shiftTail(z3, j - 1);        // first shift
    var s2 = this.gotoBlock(e1, j - 1);         // start of the block after the gap
    var g1 = this.fresh(); this.q(s2, '1', 'L', g1);
    var g = this.fresh(); this.q(g1, 'B', 'L', g);
    return this.shiftTail(g, j - 1);            // second shift
  };
  // Add a stroke to the last block
  Builder.prototype.incLast = function (e) {
    var t = this.fresh(), u = this.fresh(), v = this.fresh(), x = this.fresh();
    this.q(e, 'B', 'L', t); this.q(t, 'B', '1', u); this.q(u, '1', 'R', v); this.q(v, 'B', 'R', x);
    return x;
  };
  // Test whether the j-th block codes 0; returns [exitZero, exitNonZero], both at E
  Builder.prototype.testZero = function (e, j) {
    var s = this.gotoBlock(e, j);
    var a = this.fresh(); this.q(s, '1', 'R', a);
    var z = this.fresh(), nz = this.fresh();
    this.q(a, 'B', 'B', z); this.q(a, '1', '1', nz);
    return [this.gotoEnd(z), this.gotoEnd(nz)];
  };

  // Compile f: precondition E with the arguments = the last n blocks;
  // postcondition E with one more block coding f(arguments).
  Builder.prototype.compile = function (e, f) {
    var self = this, cur = e, i, j;
    switch (f.t) {
      case 'const': return this.append(e, f.m);
      case 'succ': return this.incLast(this.copy(e, 1));
      case 'proj': return this.copy(e, f.k - f.i + 1);
      case 'comp': {
        var m = arity(f.hs[0]), k = f.hs.length;
        for (j = 1; j <= k; j++) {
          for (i = 1; i <= m; i++) cur = this.copy(cur, m + j - 1);
          cur = this.compile(cur, f.hs[j - 1]);
          for (i = 0; i < m; i++) cur = this.del(cur, 2);
        }
        cur = this.compile(cur, f.g);
        for (i = 0; i < k; i++) cur = this.del(cur, 2);
        return cur;
      }
      case 'rec': {
        var kk = arity(f.g) + 1;              // arity of f
        cur = this.copy(cur, kk);               // cnt := y
        cur = this.append(cur, 0);              // i := 0
        for (i = 0; i < kk - 1; i++) cur = this.copy(cur, kk + 1);
        cur = this.compile(cur, f.g);           // acc := g(x)
        for (i = 0; i < kk - 1; i++) cur = this.del(cur, 2);
        var loop = cur;
        var t = this.testZero(loop, 3);
        // cnt = 0: remove cnt and i
        var done = this.del(this.del(t[0], 3), 2);
        // otherwise: loop body
        cur = this.dec(t[1], 3);
        cur = this.copy(cur, 2);                // i
        cur = this.copy(cur, 2);                // acc
        for (i = 0; i < kk - 1; i++) cur = this.copy(cur, kk + 4);
        cur = this.compile(cur, f.h);           // r := h(i, acc, x)
        for (i = 0; i < kk + 1; i++) cur = this.del(cur, 2);
        cur = this.copy(cur, 3);                // i
        cur = this.incLast(cur);                // i+1
        cur = this.copy(cur, 2);                // r
        for (i = 0; i < 3; i++) cur = this.del(cur, 3);
        this.link(cur, loop);
        return done;
      }
      case 'mu': {
        var n = arity(f.g) - 1;
        cur = this.append(cur, 0);              // y := 0
        var lp = cur;
        cur = lp;
        for (i = 0; i <= n; i++) cur = this.copy(cur, n + 1);
        cur = this.compile(cur, f.g);
        for (i = 0; i <= n; i++) cur = this.del(cur, 2);
        var tz = this.testZero(cur, 1);
        var fin = this.del(tz[0], 1);
        var again = this.incLast(this.del(tz[1], 1));
        this.link(again, lp);
        return fin;
      }
    }
    throw new Error('unknown term');
  };

  // Complete machine, in the standard format of the chapter "Turing machines"
  function compileToTM(f) {
    var b = new Builder();
    var n = arity(f);
    var start = 0;
    var e = b.gotoEnd(start);
    e = b.compile(e, f);
    for (var i = 0; i < n; i++) e = b.del(e, 2);   // erase the arguments
    // remove a stroke from the result: the number of strokes is then f(x)
    var t = b.fresh(), u = b.fresh(), x = b.fresh();
    b.q(e, 'B', 'L', t); b.q(t, 'B', 'L', u); b.q(u, '1', 'B', x);
    // rename to q0, q1, ... in order of appearance
    var names = { 0: 'q0' }, cnt = 1;
    function nm(s) { if (!(s in names)) names[s] = 'q' + (cnt++); return names[s]; }
    var quads = b.quads.map(function (qd) { return [nm(qd[0]), qd[1], qd[2], nm(qd[3])]; });
    return { quads: quads, states: cnt };
  }

  /* Small library of terms */
  var C = function (k, m) { return { t: 'const', k: k, m: m }; };
  var S = { t: 'succ' };
  var A = function (k, i) { return { t: 'proj', k: k, i: i }; };
  var comp = function (g) { return { t: 'comp', g: g, hs: Array.prototype.slice.call(arguments, 1) }; };
  var rec = function (g, h) { return { t: 'rec', g: g, h: h }; };
  var mu = function (g) { return { t: 'mu', g: g }; };
  var lib = {};
  lib.add = rec(A(1, 1), comp(S, A(3, 2)));                       // add(0,y)=y ; add(x+1,y)=S(add(x,y))
  lib.mult = rec(C(1, 0), comp(lib.add, A(3, 3), A(3, 2)));       // mult(0,y)=0 ; mult(x+1,y)=y+mult(x,y)
  lib.pred = rec(C(0, 0), A(2, 1));                               // pred(0)=0 ; pred(y+1)=y
  // monus(x, y) = y ∸ x  (recursion on the first argument)
  lib.monusRev = rec(A(1, 1), comp(lib.pred, A(3, 2)));
  lib.monus = comp(lib.monusRev, A(2, 2), A(2, 1));                // monus(a,b) = a ∸ b
  lib.sg = rec(C(0, 0), C(2, 1));                                 // sg(0)=0 ; sg(y+1)=1
  lib.sgbar = rec(C(0, 1), C(2, 0));
  // div(x, y) = mu z [ sgbar( (z+1)*y ∸ x ) ] : least z with (z+1)y > x  (undefined if y = 0)
  lib.div = mu(comp(lib.sgbar, comp(lib.monus, comp(lib.mult, comp(S, A(3, 3)), A(3, 2)), A(3, 1))));
  // power: t(y, x) = x^y by recursion on y, then permutation of the arguments
  lib.powRev = rec(C(1, 1), comp(lib.mult, A(3, 3), A(3, 2)));
  lib.pow = comp(lib.powRev, A(2, 2), A(2, 1));                    // pow(x, y) = x^y
  lib.fact = rec(C(0, 1), comp(lib.mult, comp(S, A(2, 1)), A(2, 2))); // 0! = 1 ; (y+1)! = (y+1) × y!
  lib.eq = comp(lib.sgbar, comp(lib.add, lib.monus, comp(lib.monus, A(2, 2), A(2, 1)))); // χ=(x,y) = sgbar(|x−y|)
  // everywhere undefined function: mu z [ 1 ]
  lib.vide = mu(C(2, 1));

  var api = {
    parseQuads: parseQuads, parseQuints: parseQuints, QuadMachine: QuadMachine, encodeArgs: encodeArgs,
    countOnes: countOnes, describe: describe, runRado: runRado,
    compileToTM: compileToTM, evalTerm: evalTerm, arity: arity, show: show,
    terms: { C: C, S: S, A: A, comp: comp, rec: rec, mu: mu }, lib: lib
  };
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  else root.Turing = api;
})(this);
