/* Poker Angel — push/fold and ICM (renderer/pushfold.js). Pure maths, no page code.
   Short-stacked tournament poker comes down to one decision: all-in or fold. This file holds
     · the 169×169 starting-hand equity table (computed by scripts/build-pushfold.js, shipped in
       pushfold-data.js) and the card-removal weights between hand classes;
     · the equilibrium (Nash) push/fold solver: for each stack depth, the shoving range nobody can
       exploit and the calling ranges that answer it (also precomputed into pushfold-data.js);
     · ICM — what a stack is worth in prize money (Malmuth-Harville) — and the spot evaluator
       that grades a real tournament all-in in prize equity, next to the chip-only answer.
   Units are big blinds. The ante is a big-blind ante (BBA, 1bb, paid by the big blind as dead
   money) — the WSOP standard.
   Deps: logic-poker.js (PK_HAND_ORDER). Data: pushfold-data.js (PF_DATA) when it is loaded. */

const PushFold = (() => {
  const RK = '23456789TJQKA';
  const N = 169;
  const CLASSES = () => PK_HAND_ORDER;
  let _ix = null;
  const ix = k => { if (!_ix) { _ix = {}; CLASSES().forEach((c, i) => { _ix[c] = i; }); } return _ix[k]; };
  // card ids 0..51 = (rank-2)*4 + suit
  function combosOfClass(k) {
    const a = RK.indexOf(k[0]), b = RK.indexOf(k[1]), out = [];
    if (k.length === 2) { for (let s = 0; s < 4; s++) for (let t = s + 1; t < 4; t++) out.push([a * 4 + s, b * 4 + t]); }
    else if (k[2] === 's') { for (let s = 0; s < 4; s++) out.push([a * 4 + s, b * 4 + s]); }
    else { for (let s = 0; s < 4; s++) for (let t = 0; t < 4; t++) if (s !== t) out.push([a * 4 + s, b * 4 + t]); }
    return out;
  }
  // W[h*N+v] = how many combos of class v are still possible, on average, when you hold a combo of h.
  let _W = null, _Wsum = null;
  function weights() {
    if (_W) return _W;
    const C = CLASSES().map(combosOfClass);
    _W = new Float32Array(N * N); _Wsum = new Float32Array(N);
    for (let h = 0; h < N; h++) for (let v = 0; v < N; v++) {
      let n = 0;
      for (const x of C[h]) for (const y of C[v]) if (x[0] !== y[0] && x[0] !== y[1] && x[1] !== y[0] && x[1] !== y[1]) n++;
      _W[h * N + v] = n / C[h].length; _Wsum[h] += _W[h * N + v];
    }
    return _W;
  }
  // ---- the equity table (h's all-in equity against v, preflop) ----
  let _EQ = null;
  function b64ToBytes(s) {
    if (typeof atob === 'function') { const bin = atob(s); const u = new Uint8Array(bin.length); for (let i = 0; i < bin.length; i++) u[i] = bin.charCodeAt(i); return u; }
    return new Uint8Array(Buffer.from(s, 'base64'));
  }
  function setEquityTable(eq) { _EQ = eq; }
  function eqTable() {
    if (_EQ) return _EQ;
    if (typeof PF_DATA === 'undefined' || !PF_DATA.eq) throw new Error('push/fold data not loaded');
    const bytes = b64ToBytes(PF_DATA.eq), u16 = new Uint16Array(bytes.buffer, bytes.byteOffset, bytes.length / 2);
    _EQ = new Float32Array(N * N);
    for (let i = 0; i < N * N; i++) _EQ[i] = u16[i] / 65535;
    return _EQ;
  }
  // Equity of class h against a range given as per-class frequencies (0..1), card removal included.
  function eqVsRange(h, freq) {
    const W = weights(), EQ = eqTable(); let num = 0, den = 0;
    for (let v = 0; v < N; v++) { const w = W[h * N + v] * freq[v]; if (w) { num += w * EQ[h * N + v]; den += w; } }
    return den ? num / den : 0.5;
  }
  // How often a range holds a hand, given that you hold h (0..1).
  function rangeShare(h, freq) {
    const W = weights(); let n = 0;
    for (let v = 0; v < N; v++) n += W[h * N + v] * freq[v];
    return n / _Wsum[h];
  }

  // ---- equilibrium push/fold (chip EV) ----
  // The pusher has m players behind; all stacks are S bb (before posting). Blinds: the last player
  // behind is the BB (1), the one before the SB (0.5); with m = 1 the pusher IS the SB. The BB
  // also posts a 1bb ante as dead money. Callers are taken one at a time (an overcall after a call
  // is rare enough to leave out). Solved by fictitious play: each side repeatedly best-responds to
  // the other's average strategy, which converges on the equilibrium.
  function blindOfCaller(m, j) { return j === m ? 1 : (j === m - 1 && m >= 2 ? 0.5 : 0); }
  function solve(m, S, opts) {
    opts = opts || {};
    const ante = opts.ante == null ? 1 : opts.ante, iters = opts.iters || 300;
    const W = weights(), EQ = eqTable();
    const bp = m === 1 ? 0.5 : 0, D = 1.5 + ante;
    const push = new Float64Array(N).fill(0.5), call = [];
    for (let j = 1; j <= m; j++) call[j] = new Float64Array(N).fill(0.3);
    const pc = new Float64Array(m + 1), eqc = new Float64Array(m + 1);
    for (let t = 1; t <= iters; t++) {
      const lr = 1 / (t + 1);
      // pusher's best response
      const brP = new Float64Array(N);
      for (let h = 0; h < N; h++) {
        for (let j = 1; j <= m; j++) {
          let wc = 0, we = 0; const cj = call[j];
          for (let v = 0; v < N; v++) { const w = W[h * N + v] * cj[v]; wc += w; we += w * EQ[h * N + v]; }
          pc[j] = wc / _Wsum[h]; eqc[j] = wc ? we / wc : 0;
        }
        let reach = 1, ev = 0;
        for (let j = 1; j <= m; j++) { const pot = 2 * S + D - bp - blindOfCaller(m, j); ev += reach * pc[j] * eqc[j] * pot; reach *= (1 - pc[j]); }
        ev += reach * (S + D - bp);
        brP[h] = ev > S - bp ? 1 : 0;
      }
      // callers' best responses to the pusher's range
      for (let j = 1; j <= m; j++) {
        const bj = blindOfCaller(m, j), pot = 2 * S + D - bp - bj, cj = call[j];
        for (let v = 0; v < N; v++) {
          let wp = 0, we = 0;
          for (let h = 0; h < N; h++) { const w = W[v * N + h] * push[h]; wp += w; we += w * EQ[v * N + h]; }
          const br = wp && (we / wp) * pot > S - bj ? 1 : 0;
          cj[v] += (br - cj[v]) * lr;
        }
      }
      for (let h = 0; h < N; h++) push[h] += (brP[h] - push[h]) * lr;
    }
    return { push, call };
  }

  // ---- the precomputed tables ----
  // PF_DATA.push[m][S-1] / PF_DATA.call[m + '-' + j][S-1]: 169-bit hex strings in PK_HAND_ORDER order.
  const MAX_S = 20;
  const bitsToFreq = hex => { const f = new Float64Array(N); for (let i = 0; i < N; i++) f[i] = (parseInt(hex[i >> 2], 16) >> (3 - (i & 3))) & 1; return f; };
  function freqToBits(freq) { let s = ''; for (let i = 0; i < N; i += 4) { let n = 0; for (let k = 0; k < 4; k++) n = n * 2 + ((i + k < N && freq[i + k] >= 0.5) ? 1 : 0); s += n.toString(16); } return s; }
  const clampS = S => Math.max(1, Math.min(MAX_S, Math.round(S)));
  const _cache = {};
  function pushFreq(m, S) { const k = 'p' + m + '.' + clampS(S); return _cache[k] || (_cache[k] = bitsToFreq(PF_DATA.push[m][clampS(S) - 1])); }
  function callFreq(m, j, S) { const k = 'c' + m + '-' + j + '.' + clampS(S); return _cache[k] || (_cache[k] = bitsToFreq(PF_DATA.call[m + '-' + j][clampS(S) - 1])); }
  const inPush = (k, m, S) => pushFreq(m, S)[ix(k)] >= 0.5;
  const inCall = (k, m, j, S) => callFreq(m, j, S)[ix(k)] >= 0.5;
  // Largest stack (bb, up to 20) at which hand k is still a push / a call — the classic chart number.
  function maxPush(k, m) { let best = 0; for (let S = 1; S <= MAX_S; S++) if (inPush(k, m, S)) best = S; return best; }
  function maxCall(k, m, j) { let best = 0; for (let S = 1; S <= MAX_S; S++) if (inCall(k, m, j, S)) best = S; return best; }
  const rangePct = freq => { let n = 0; CLASSES().forEach((c, i) => { if (freq[i] >= 0.5) n += c.length === 2 ? 6 : (c[2] === 's' ? 4 : 12); }); return n / 1326; };

  // ---- ICM: what each stack is worth in prize money (Malmuth-Harville) ----
  function icm(stacks, payouts) {
    const n = stacks.length, out = new Array(n).fill(0);
    const pays = payouts.slice(0, n);
    const memo = new Map();
    // value[i] for players in `mask` competing for places from `place` on
    function rec(mask, place) {
      if (place >= pays.length || !mask) return null;
      const key = mask * 16 + place;
      if (memo.has(key)) return memo.get(key);
      const res = new Array(n).fill(0);
      let tot = 0; for (let i = 0; i < n; i++) if (mask & (1 << i)) tot += stacks[i];
      const members = []; for (let i = 0; i < n; i++) if (mask & (1 << i)) members.push(i);
      for (const i of members) {
        const p = tot > 0 ? stacks[i] / tot : 1 / members.length;
        if (!p) continue;
        res[i] += p * pays[place];
        const sub = rec(mask & ~(1 << i), place + 1);
        if (sub) for (let k = 0; k < n; k++) res[k] += p * sub[k];
      }
      memo.set(key, res);
      return res;
    }
    const r = rec((1 << n) - 1, 0);
    if (r) for (let i = 0; i < n; i++) out[i] = r[i];
    return out;
  }

  // ---- grading a real tournament all-in ----
  // table: { stacks: [bb behind, after posting], posted: [bb already in the pot], dead: ante money (bb),
  //          payouts: [prize per place],
  //          hero: seat, order: [seats still to act after hero, in order], bb: seat of the big blind }
  // Returns hero's prize equity for shove vs fold, the chip-EV versions, and each caller's numbers.
  function outcome(t, a, b, aWins) {   // a and b all-in against each other; everyone else's posts are dead money
    const s = t.stacks.slice(), Ta = s[a] + t.posted[a], Tb = s[b] + t.posted[b], X = Math.min(Ta, Tb);
    const dead = t.posted.reduce((x, y) => x + y, 0) - t.posted[a] - t.posted[b] + (t.dead || 0), pot = 2 * X + dead;
    s[a] = Ta - X + (aWins ? pot : 0); s[b] = Tb - X + (aWins ? 0 : pot);
    return s;
  }
  function steal(t, a) { const s = t.stacks.slice(); s[a] += t.posted.reduce((x, y) => x + y, 0) + (t.dead || 0); return s; }
  function giveTo(t, a) { return steal(t, a); }
  function shoveSpot(t, heroClass, opts) {
    opts = opts || {};
    const h = ix(heroClass), hero = t.hero, m = t.order.length;
    const S = Math.min(t.stacks[hero] + t.posted[hero], Math.max.apply(null, t.order.map(j => t.stacks[j] + t.posted[j])));
    const heroRange = pushFreq(m, S);                               // what the callers expect hero to shove
    const $ = s => icm(s, t.payouts);
    const fold = $(giveTo(t, t.bb)), stealS = $(steal(t, hero));
    const chipsFold = t.stacks[hero], chipsSteal = steal(t, hero)[hero];
    const callers = [];
    let reach = 1, evI = 0, evC = 0;
    for (const j of t.order) {
      const win = outcome(t, hero, j, true), lose = outcome(t, hero, j, false);
      const iw = $(win), il = $(lose);
      // Caller j's break-even equity: calling must beat folding (then hero takes the blinds). For the
      // caller, "win" is the outcome where hero loses.
      const cWin = il[j], cLose = iw[j], cFold = stealS[j];
      const needI = (cFold - cLose) / Math.max(1e-9, cWin - cLose);
      const potJ = lose[j] - (t.stacks[j] + t.posted[j] - Math.min(t.stacks[hero] + t.posted[hero], t.stacks[j] + t.posted[j]));
      const riskJ = Math.min(t.stacks[hero] + t.posted[hero], t.stacks[j] + t.posted[j]) - t.posted[j];
      const needC = riskJ / Math.max(1e-9, potJ);
      const callFreqJ = new Float64Array(N);
      for (let v = 0; v < N; v++) callFreqJ[v] = eqVsRange(v, heroRange) >= (opts.chipOnly ? needC : needI) ? 1 : 0;
      const pc = rangeShare(h, callFreqJ), eqc = pc ? eqVsRange(h, callFreqJ) : 0;
      evI += reach * pc * (eqc * iw[hero] + (1 - eqc) * il[hero]);
      evC += reach * pc * (eqc * win[hero] + (1 - eqc) * lose[hero]);
      callers.push({ seat: j, needIcm: needI, needChips: needC, callPct: rangePct(callFreqJ), pc, eqWhenCalled: eqc, win$: iw[hero], lose$: il[hero], winChips: win[hero], loseChips: lose[hero] });
      reach *= (1 - pc);
    }
    evI += reach * stealS[hero]; evC += reach * chipsSteal;
    return { shove$: evI, fold$: fold[hero], steal$: stealS[hero], shoveChips: evC, foldChips: chipsFold, stealChips: chipsSteal, foldEquity: reach, callers, heroRangePct: rangePct(heroRange), S };
  }
  // Hero facing an all-in from `pusher` (who had `pusherBehind` players behind them when they shoved).
  function callSpot(t, heroClass, pusher, pusherBehind) {
    const h = ix(heroClass), hero = t.hero;
    const Sp = Math.min(t.stacks[pusher] + t.posted[pusher], t.stacks[hero] + t.posted[hero]);
    const range = pushFreq(Math.max(1, pusherBehind), t.stacks[pusher] + t.posted[pusher]);
    const eq = eqVsRange(h, range);
    const $ = s => icm(s, t.payouts);
    const win = outcome(t, hero, pusher, true), lose = outcome(t, hero, pusher, false), fold = steal(t, pusher);
    const iw = $(win)[hero], il = $(lose)[hero], ifold = $(fold)[hero];
    const needIcm = (ifold - il) / Math.max(1e-9, iw - il);
    const risk = Sp - t.posted[hero], pot = win[hero] - (t.stacks[hero] + t.posted[hero] - Sp);
    const needChips = risk / Math.max(1e-9, pot);
    return { eq, needIcm, needChips, call$: eq * iw + (1 - eq) * il, fold$: ifold, win$: iw, lose$: il, pusherRangePct: rangePct(range), S: Sp };
  }

  return { N, CLASSES, ix, combosOfClass, weights, setEquityTable, eqTable, eqVsRange, rangeShare, solve, freqToBits, bitsToFreq, pushFreq, callFreq, inPush, inCall, maxPush, maxCall, rangePct, icm, shoveSpot, callSpot, MAX_S };
})();

if (typeof module !== 'undefined' && module.exports) module.exports = PushFold;
