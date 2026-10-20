/* Poker Angel — the poker maths (renderer/logic-poker.js). Pure: table-read parsing, the hand
   evaluator, Monte-Carlo equity and the starting-hand order. Money and odds are computed HERE, in
   code, never by the model. Unit-tested in test/logic-poker.test.js. */

// ---- Poker Angel: the table read and its maths ----------------------------------------------------
// The coach (vision) reads the table into a ```json block; the arithmetic on it is done HERE, in
// code, never by the model — the same rule as statements. Returns { state, rest } where rest is the
// coaching prose with the block removed; state is null when no usable block was found.
function parsePokerState(text) {
  const s = String(text || '');
  const m = s.match(/```(?:json)?\s*(\{[\s\S]*?\})\s*```/i);
  if (!m) return { state: null, rest: s.trim() };
  let state = null;
  try { state = JSON.parse(m[1]); } catch (e) { state = null; }
  if (!state || typeof state !== 'object' || Array.isArray(state)) state = null;
  return { state, rest: (s.slice(0, m.index) + s.slice(m.index + m[0].length)).trim() };
}
const _pkNum = v => { const n = typeof v === 'number' ? v : parseFloat(String(v == null ? '' : v).replace(/[^0-9.\-]/g, '')); return isFinite(n) ? n : null; };
// pot = everything in the middle INCLUDING this street's bets; toCall = what hero must add.
// Required equity = toCall ÷ (pot + toCall). Effective stack = the smaller of hero's stack and the
// biggest stack still in the hand against them. Stacks are what's BEHIND (not counting bets out).
function pokerMaths(state) {
  if (!state) return null;
  const stakes = state.stakes || {};
  const bb = _pkNum(stakes.bb);
  const pot = _pkNum(state.pot);
  const toCall = _pkNum(state.toCall);
  const hero = state.hero || {};
  const heroStack = _pkNum(hero.stack);
  const live = (Array.isArray(state.seats) ? state.seats : [])
    .filter(x => x && !x.isHero && /^(active|allin|all-in)$/i.test(String(x.status || '')))
    .map(x => _pkNum(x.stack) + (_pkNum(x.bet) || 0)).filter(v => v != null);
  const heroTotal = heroStack != null ? heroStack + (_pkNum(hero.bet) || 0) : null;
  const eff = heroTotal != null && live.length ? Math.min(heroTotal, Math.max.apply(null, live)) : null;
  const inBB = v => (v != null && bb > 0) ? Math.round(v / bb * 10) / 10 : null;
  const r1 = v => v == null ? null : Math.round(v * 1000) / 10;   // fraction → % with one decimal
  return {
    bb: bb > 0 ? bb : null,
    potBB: inBB(pot), toCallBB: inBB(toCall), heroBB: inBB(heroStack), effBB: inBB(eff), eff,
    needEquityPct: (toCall > 0 && pot != null && pot >= 0) ? r1(toCall / (pot + toCall)) : null,
    spr: (eff != null && pot > 0) ? Math.round(eff / pot * 10) / 10 : null,
    activeOpponents: live.length,
  };
}

// ---- Poker Angel: hand evaluator + Monte-Carlo equity (Hold'em) ------------------------------------
// The coach must not guess the single most important number. Cards are {r: 2..14, s: 0..3}.
const PK_RANKS = '23456789TJQKA', PK_SUITS = 'shdc';
function parseCard(c) {
  const m = String(c || '').trim().match(/^(10|[2-9TJQKA])\s*([shdc♠♥♦♣])$/i);
  if (!m) return null;
  const r = PK_RANKS.indexOf(m[1] === '10' ? 'T' : m[1].toUpperCase()) + 2;
  const s = 'shdc♠♥♦♣'.indexOf(m[2].toLowerCase()) % 4;
  return r >= 2 ? { r, s } : null;
}
function _pkStraightHigh(mask) {
  if (mask & (1 << 14)) mask |= 2;                       // the ace also plays low (A-2-3-4-5)
  for (let h = 14; h >= 5; h--) { const m = 31 << (h - 4); if ((mask & m) === m) return h; }
  return 0;
}
function _pkScore(cat, ks) { let v = cat; for (let i = 0; i < 5; i++) v = v * 15 + (ks[i] || 0); return v; }
// Best five-card hand from 5–7 cards → a number; higher wins, equal ties.
// Categories: 8 straight flush · 7 quads · 6 full house · 5 flush · 4 straight · 3 trips · 2 two pair · 1 pair · 0 high card.
function evalHand(cards) {
  const cnt = new Array(15).fill(0), sMask = [0, 0, 0, 0], sCnt = [0, 0, 0, 0];
  let mask = 0;
  for (const c of cards) { cnt[c.r]++; mask |= 1 << c.r; sMask[c.s] |= 1 << c.r; sCnt[c.s]++; }
  let flush = null;
  for (let s = 0; s < 4; s++) if (sCnt[s] >= 5) {
    const sh = _pkStraightHigh(sMask[s]); if (sh) return _pkScore(8, [sh]);
    flush = []; for (let r = 14; r >= 2 && flush.length < 5; r--) if (sMask[s] & (1 << r)) flush.push(r);
  }
  const quads = [], trips = [], pairs = [], singles = [];
  for (let r = 14; r >= 2; r--) { const n = cnt[r]; if (n === 4) quads.push(r); else if (n === 3) trips.push(r); else if (n === 2) pairs.push(r); else if (n === 1) singles.push(r); }
  const kick = (excl, k) => { const out = []; for (let r = 14; r >= 2 && out.length < k; r--) if (cnt[r] && excl.indexOf(r) < 0) out.push(r); return out; };
  if (quads.length) return _pkScore(7, [quads[0]].concat(kick([quads[0]], 1)));
  if (trips.length && (trips.length > 1 || pairs.length)) return _pkScore(6, [trips[0], Math.max(trips[1] || 0, pairs[0] || 0)]);
  if (flush) return _pkScore(5, flush);
  const sh = _pkStraightHigh(mask); if (sh) return _pkScore(4, [sh]);
  if (trips.length) return _pkScore(3, [trips[0]].concat(kick([trips[0]], 2)));
  if (pairs.length > 1) return _pkScore(2, [pairs[0], pairs[1]].concat(kick([pairs[0], pairs[1]], 1)));
  if (pairs.length) return _pkScore(1, [pairs[0]].concat(kick([pairs[0]], 3)));
  return _pkScore(0, kick([], 5));
}
// The 169 starting hands, strongest first (all-in equity vs one random hand; generated offline with
// evalHand, 20k trials per hand). Used to turn "top X% of hands" into a concrete range.
const PK_HAND_ORDER = 'AA KK QQ JJ TT 99 88 AKs 77 AQs AKo AJs ATs AQo AJo ATo 66 KQs A9s A8s KJs KTs A7s 55 KQo A9o A8o A6s KJo A5s KTo K9s A4s A7o QJs A3s QTs K8s K7s A6o A2s K9o A5o 44 A4o K6s QJo JTs Q9s QTo K8o A3o K7o K5s K4s A2o Q8s JTo Q9o K6o K3s J9s Q7s K2s 33 K5o J8s T9s Q6s Q8o K4o J9o J7s Q5s Q4s Q7o T8s K3o K2o T9o 22 T7s Q3s J8o J6s Q6o Q2s 98s J7o J5s J4s T8o Q5o Q4o T6s 97s T7o J3s J6o Q3o 98o 87s J2s Q2o T5s T4s J5o 97o T6o 96s J4o 86s T3s 76s T2s 87o J3o 95s T5o J2o 85s T4o 96o 75s 65s 86o 94s 84s T3o 76o T2o 93s 54s 74s 95o 64s 92s 85o 83s 75o 73s 82s 94o 65o 53s 84o 63s 93o 54o 74o 72s 64o 92o 43s 52s 62s 42s 83o 82o 73o 53o 32s 63o 72o 43o 52o 62o 42o 32o'.split(' ');
const _PK_PCT = (() => {   // class → percentile (0..1) of the 1326 starting combinations it sits at
  const out = {}; let acc = 0;
  for (const h of PK_HAND_ORDER) { acc += h.length === 2 ? 6 : (h[2] === 's' ? 4 : 12); out[h] = acc / 1326; }
  return out;
})();
function handClass(a, b) {
  const hi = a.r >= b.r ? a : b, lo = hi === a ? b : a;
  const k = PK_RANKS[hi.r - 2] + PK_RANKS[lo.r - 2];
  return hi.r === lo.r ? k : k + (a.s === b.s ? 's' : 'o');
}
// Rough range width from what a player has DONE this hand — an estimate, labelled as one in the UI.
function rangeFromAction(seat) {
  const a = String((seat && (seat.lastAction || '')) || '').toLowerCase();
  if (/all.?in|shove|jam|4-?bet|5-?bet/.test(a)) return 0.06;
  if (/3-?bet|re-?raise/.test(a)) return 0.09;
  if (/raise|bet|lead/.test(a)) return 0.2;
  if (/call|limp/.test(a)) return 0.35;
  return 0.6;   // checked / no action yet
}
// Monte-Carlo all-in equity. hero: 2 cards, board: 0–5 cards, opponents: array of range fractions
// (1 = any two cards). rng is injectable so tests are deterministic.
function equityMC(heroStrs, boardStrs, opponents, trials, rng) {
  rng = rng || Math.random; trials = trials || 6000;
  const hero = (heroStrs || []).map(parseCard), board = (boardStrs || []).map(parseCard);
  if (hero.length !== 2 || hero.some(c => !c) || board.some(c => !c) || board.length > 5 || !opponents || !opponents.length) return null;
  const used = new Set(hero.concat(board).map(c => c.r * 4 + c.s));
  if (used.size !== hero.length + board.length) return null;           // a duplicated card = a misread
  const deck = []; for (let r = 2; r <= 14; r++) for (let s = 0; s < 4; s++) if (!used.has(r * 4 + s)) deck.push({ r, s });
  // each opponent's possible hands: every combo of the deck within their width (built once)
  const lists = opponents.map(width => { const out = []; for (let i = 0; i < deck.length; i++) for (let j = i + 1; j < deck.length; j++) if (width >= 1 || _PK_PCT[handClass(deck[i], deck[j])] <= width) out.push([deck[i], deck[j]]); return out.length ? out : [[deck[0], deck[1]]]; });
  let won = 0;
  for (let t = 0; t < trials; t++) {
    const d = deck.slice(); let n = d.length; const taken = new Set();
    const draw = () => { const i = Math.floor(rng() * n); const c = d[i]; d[i] = d[--n]; return c; };
    const opp = [];
    for (let k = 0; k < opponents.length; k++) {
      // a hand from the top `width` of starting hands, picked directly from the list (no giving up)
      const list = lists[k]; let a = null, b = null;
      for (let tries = 0; tries < 20 && !a; tries++) { const c = list[Math.floor(rng() * list.length)]; if (!taken.has(c[0].r * 4 + c[0].s) && !taken.has(c[1].r * 4 + c[1].s)) { a = c[0]; b = c[1]; } }
      if (!a) { a = draw(); b = draw(); } else { taken.add(a.r * 4 + a.s); taken.add(b.r * 4 + b.s); for (let i = 0; i < n; i++) if ((d[i].r === a.r && d[i].s === a.s) || (d[i].r === b.r && d[i].s === b.s)) { d[i] = d[--n]; i--; } }
      opp.push([a, b]);
    }
    const full = board.slice(); while (full.length < 5) full.push(draw());
    const hs = evalHand(hero.concat(full));
    let best = -1, ties = 0;
    for (const o of opp) { const v = evalHand(o.concat(full)); if (v > best) { best = v; ties = 0; } if (v === best) ties++; }
    if (hs > best) won += 1; else if (hs === best) won += 1 / (ties + 1);
  }
  return Math.round(won / trials * 1000) / 10;
}

// Node (tests) only — in the page this is a classic <script>, so these stay global.
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { parsePokerState, pokerMaths, parseCard, evalHand, equityMC, handClass, rangeFromAction, PK_HAND_ORDER };
}
