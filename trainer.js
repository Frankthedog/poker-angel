/* Poker Angel — the trainer (renderer/trainer.js).
   A practice table and a set of drills, all against the computer: no site, no money, no one else.
   🃏 Play: 8-handed No-Limit Hold'em, blinds 0.5/1, everyone 100bb deep every hand, you against seven
   bots that each play a recognisable style. Every decision you make is graded the moment you make it:
   preflop against opening / 3-bet charts, postflop on your equity against each opponent's likely
   range (Monte Carlo, narrowed by what they have done this hand) and the pot odds.
   Drills: preflop charts, pot odds, equity estimation, outs, reading the winner at showdown.
   The maths is code, never the model (the same rule as the coach). The AI coach
   is optional: it explains a FINISHED hand it is handed, with the code's numbers in it.
   Deps: logic-poker.js (evalHand, PK_HAND_ORDER), core.js ($/toast/escapeHtml), window.api.draft.
   Wired from app.js. The engine is pure and tested on its own (test/trainer.test.js). */

const Trainer = (() => {
  const RK = '23456789TJQKA', SU = 'shdc', SYM = { s: '♠', h: '♥', d: '♦', c: '♣' };
  const POS = ['BTN', 'SB', 'BB', 'UTG', 'UTG+1', 'LJ', 'HJ', 'CO'];   // by seat distance from the button (8 players)
  const NSEATS = POS.length;
  const STREET = ['Preflop', 'Flop', 'Turn', 'River'];
  const CAT = 759375;    // 15^5: evalHand's score is category * CAT + kickers
  const STATS_KEY = 'pokerangel.trainer.stats', OPT_KEY = 'pokerangel.trainer.opts';
  const cid = c => (c.r - 2) * 4 + c.s;
  const fromId = id => ({ r: (id >> 2) + 2, s: id & 3 });
  const r1 = v => Math.round(v * 10) / 10;
  const half = v => Math.round(v * 2) / 2;
  const bbs = v => { const x = Math.round(v * 100) / 100; return String(x) + 'bb'; };
  const cardTxt = c => (c.r === 10 ? '10' : RK[c.r - 2]) + SYM[SU[c.s]];
  const cardsTxt = cs => cs.map(cardTxt).join(' ');
  // A seeded shuffle source (mulberry32): the same seed deals the same cards on every machine.
  const mulberry = (seed) => { let s = seed >>> 0; return () => { s = (s + 0x6D2B79F5) >>> 0; let t = s; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; }; };
  function shuffled(rng) {
    const d = []; for (let id = 0; id < 52; id++) d.push(fromId(id));
    for (let i = d.length - 1; i > 0; i--) { const j = Math.floor(rng() * (i + 1)); const t = d[i]; d[i] = d[j]; d[j] = t; }
    return d;
  }

  // ---- starting hands and ranges --------------------------------------------------------------
  function cls(a, b) {
    const hi = a.r >= b.r ? a : b, lo = hi === a ? b : a;
    const k = RK[hi.r - 2] + RK[lo.r - 2];
    return hi.r === lo.r ? k : k + (a.s === b.s ? 's' : 'o');
  }
  const combosOf = k => k.length === 2 ? 6 : (k[2] === 's' ? 4 : 12);
  let _pct = null, _combos = null;
  function pct() {   // class → the share of all 1326 combos at or above it in PK_HAND_ORDER
    if (_pct) return _pct;
    _pct = {}; let acc = 0;
    for (const h of PK_HAND_ORDER) { acc += combosOf(h); _pct[h] = acc / 1326; }
    return _pct;
  }
  function combos() {   // all 1326 two-card combos, strongest class first: a range of width w is the first w*1326
    if (_combos) return _combos;
    const order = {}; PK_HAND_ORDER.forEach((h, i) => { order[h] = i; });
    const all = [];
    for (let a = 0; a < 52; a++) for (let b = a + 1; b < 52; b++) { const x = fromId(a), y = fromId(b); all.push({ a, b, x, y, o: order[cls(x, y)] }); }
    all.sort((p, q) => p.o - q.o);
    return (_combos = all);
  }
  // Range notation: "22+", "99-55", "A2s+", "KJs-KTs", "ATo+", "T9s".
  function parseRange(txt) {
    const set = new Set(), ix = ch => RK.indexOf(ch);
    for (const raw of String(txt).split(',')) {
      const tok = raw.trim(); if (!tok) continue;
      let m;
      if ((m = tok.match(/^([2-9TJQKA])\1(\+)?$/))) { for (let i = ix(m[1]); i <= (m[2] ? 12 : ix(m[1])); i++) set.add(RK[i] + RK[i]); continue; }
      if ((m = tok.match(/^([2-9TJQKA])\1-([2-9TJQKA])\2$/))) { const a = ix(m[1]), b = ix(m[2]); for (let i = Math.min(a, b); i <= Math.max(a, b); i++) set.add(RK[i] + RK[i]); continue; }
      if ((m = tok.match(/^([2-9TJQKA])([2-9TJQKA])([so])(\+)?$/)) && ix(m[1]) > ix(m[2])) {
        if (m[4]) { for (let i = ix(m[2]); i < ix(m[1]); i++) set.add(m[1] + RK[i] + m[3]); } else set.add(m[1] + m[2] + m[3]);
        continue;
      }
      if ((m = tok.match(/^([2-9TJQKA])([2-9TJQKA])([so])-([2-9TJQKA])([2-9TJQKA])\3$/)) && m[1] === m[4]) {
        const a = ix(m[2]), b = ix(m[5]); for (let i = Math.min(a, b); i <= Math.max(a, b); i++) set.add(m[1] + RK[i] + m[3]);
        continue;
      }
      throw new Error('bad range token: ' + tok);
    }
    return set;
  }
  // Simplified 100bb charts — a sound baseline to learn from, not a solver's output. Opening ranges are
  // by seat: the more players still to act behind you, the tighter (Lojack = the first seat 6-handed).
  const CHARTS = {
    'rfi.UTG': '66+, A2s+, K9s+, QTs+, JTs, T9s, 98s, AJo+, KQo',
    'rfi.UTG+1': '55+, A2s+, K9s+, Q9s+, J9s+, T9s, 98s, 87s, ATo+, KJo+',
    'rfi.LJ': '44+, A2s+, K9s+, Q9s+, J9s+, T9s, 98s, 87s, 76s, 65s, ATo+, KJo+',
    'rfi.HJ': '33+, A2s+, K7s+, Q9s+, J9s+, T8s+, 97s+, 86s+, 75s+, 65s, 54s, A9o+, KTo+, QTo+, JTo',
    'rfi.CO': '22+, A2s+, K4s+, Q7s+, J7s+, T7s+, 96s+, 85s+, 75s+, 64s+, 54s, A7o+, A5o, K9o+, Q9o+, J9o+, T9o',
    'rfi.BTN': '22+, A2s+, K2s+, Q3s+, J5s+, T6s+, 96s+, 85s+, 74s+, 63s+, 53s+, 43s, A2o+, K7o+, Q8o+, J8o+, T8o+, 97o+, 87o, 76o',
    'rfi.SB': '22+, A2s+, K2s+, Q5s+, J6s+, T6s+, 96s+, 85s+, 75s+, 64s+, 54s, A2o+, K8o+, Q9o+, J9o+, T9o',
    isoLimp: '77+, A9s+, KTs+, QJs, ATo+, KQo',            // raise over limpers from the big blind
    ip3Early: 'QQ+, AKs, AKo, A5s, A4s',
    ipCallEarly: 'JJ-66, AQs-ATs, KQs, KJs, QJs, JTs, T9s, AQo',
    ip3Late: 'TT+, AJs+, KQs, AQo+, A5s-A3s, K9s, 76s',
    ipCallLate: '99-22, ATs-A6s, KJs-KTs, QTs+, J9s+, T9s, 98s, 87s, AJo, KQo',
    bb3Early: 'QQ+, AKs, AKo, A5s',
    bbCallEarly: 'JJ-22, AQs-A2s, K6s+, Q8s+, J8s+, T8s+, 97s+, 86s+, 75s+, 65s, 54s, ATo+, KTo+, QTo+, JTo',
    bb3Late: 'TT+, ATs+, KJs+, AJo+, KQo, A5s-A2s, 76s, 65s',
    bbCallLate: '99-22, A9s-A6s, K2s+, Q4s+, J6s+, T6s+, 95s+, 85s+, 74s+, 63s+, 53s+, 43s, A2o+, K6o+, Q8o+, J8o+, T8o+, 97o+, 87o, 76o, 65o',
    sb3Early: 'TT+, AQs+, AKo, A5s, KQs',
    sb3Late: '88+, A9s+, KTs+, QTs+, JTs, AJo+, KQo, A5s-A2s, 76s, 65s',
    vs3bet4: 'QQ+, AKs, AKo, A5s',
    vs3betCall: 'JJ-77, AQs-ATs, KQs, KJs, QJs, JTs, T9s, 98s, AQo',
    cold4: 'KK+, AKs', coldCall: 'QQ, AKo',
    jam4: 'KK+, AKs', call4: 'QQ, AKo', callJam: 'QQ+, AKs, AKo',
  };
  const VIEWS = [
    { id: 'rfi.UTG', name: 'UTG · first in', raise: 'rfi.UTG' },
    { id: 'rfi.UTG+1', name: 'UTG+1 · first in', raise: 'rfi.UTG+1' },
    { id: 'rfi.LJ', name: 'LJ · first in', raise: 'rfi.LJ' },
    { id: 'rfi.HJ', name: 'HJ · first in', raise: 'rfi.HJ' },
    { id: 'rfi.CO', name: 'CO · first in', raise: 'rfi.CO' },
    { id: 'rfi.BTN', name: 'BTN · first in', raise: 'rfi.BTN' },
    { id: 'rfi.SB', name: 'SB · first in', raise: 'rfi.SB' },
    { id: 'ipEarly', name: 'Later seats vs an early open (UTG to HJ)', raise: 'ip3Early', call: 'ipCallEarly' },
    { id: 'ipLate', name: 'BTN vs CO open', raise: 'ip3Late', call: 'ipCallLate' },
    { id: 'sbEarly', name: 'SB vs an early open (UTG to HJ)', raise: 'sb3Early' },
    { id: 'sbLate', name: 'SB vs CO/BTN open', raise: 'sb3Late' },
    { id: 'bbEarly', name: 'BB vs an early open (UTG to HJ)', raise: 'bb3Early', call: 'bbCallEarly' },
    { id: 'bbLate', name: 'BB vs CO/BTN/SB open', raise: 'bb3Late', call: 'bbCallLate' },
    { id: 'vs3', name: 'You opened, facing a 3-bet', raise: 'vs3bet4', call: 'vs3betCall' },
    { id: 'vs4', name: 'Facing a 4-bet', raise: 'jam4', call: 'call4' },
  ];
  const _sets = {};
  const chart = key => _sets[key] || (_sets[key] = parseRange(CHARTS[key]));
  const chartWidth = key => { let n = 0; chart(key).forEach(k => { n += combosOf(k); }); return n / 1326; };

  // ---- reading a hand on a board ---------------------------------------------------------------
  // Draws, with their outs: a flush draw (9), an open-ended straight draw (8), a gutshot (4), a
  // combination (up to 15, overlap removed). `straight` means at least a gutshot; `oesd` a real one.
  function draws(hole, board) {
    const none = { flush: false, straight: false, oesd: false, gut: false, outs: 0, name: '' };
    if (board.length < 3 || board.length >= 5) return none;
    const all = hole.concat(board);
    let flush = false, flushSuit = -1;
    for (let s = 0; s < 4; s++) if (all.filter(c => c.s === s).length === 4 && hole.some(c => c.s === s)) { flush = true; flushSuit = s; }
    const maskOf = cs => { let m = 0; for (const c of cs) m |= 1 << c.r; if (m & (1 << 14)) m |= 2; return m; };
    const mask = maskOf(all), holeMask = maskOf(hole);
    const completing = new Set();                                               // ranks that would make a straight using a hole card
    for (let lo = 1; lo <= 10; lo++) {
      let n = 0, missing = -1; for (let r = lo; r < lo + 5; r++) { if (mask & (1 << r)) n++; else missing = r; }
      if (n === 4 && (holeMask & (31 << lo)) && missing > 0) completing.add(missing === 1 ? 14 : missing);
    }
    const straight = completing.size > 0, oesd = completing.size >= 2, gut = completing.size === 1;
    let outs = (flush ? 9 : 0) + completing.size * 4;
    if (flush && straight) outs -= completing.size;                             // the straight cards of the flush suit are counted once
    const dead = all.filter(c => completing.has(c.r)).length; outs -= Math.min(dead, completing.size * 4 - (flush ? completing.size : 0));
    outs = Math.max(0, outs);
    const name = flush && oesd ? 'a flush draw and an open-ended straight draw' : flush && gut ? 'a flush draw and a gutshot' : flush ? 'a flush draw' : oesd ? 'an open-ended straight draw' : gut ? 'a gutshot straight draw' : '';
    return { flush, straight, oesd, gut, outs, name, flushSuit };
  }
  // 0 air · 1 weak pair or a draw · 2 top pair / overpair · 3 two pair or better made with a hole card.
  function tierOn(hole, board) {
    if (board.length < 3) return 1;
    const cat = Math.floor(evalHand(hole.concat(board)) / CAT), bcat = Math.floor(evalHand(board) / CAT);
    if (cat >= 3 && cat > bcat) return 3;
    if (cat === 2 && bcat === 0) return 3;
    const maxB = Math.max.apply(null, board.map(c => c.r));
    const pocket = hole[0].r === hole[1].r;
    const hit = hole.filter(h => board.some(b => b.r === h.r)).map(h => h.r);
    if (pocket && hole[0].r > maxB) return 2;
    if (hit.length && Math.max.apply(null, hit) === maxB) return 2;
    const d = draws(hole, board);
    return (pocket || hit.length || d.flush || d.straight) ? 1 : 0;
  }
  const CAT_NAME = ['High card', 'Pair', 'Two pair', 'Three of a kind', 'Straight', 'Flush', 'Full house', 'Four of a kind', 'Straight flush'];
  const ONE = { 2: 'Two', 3: 'Three', 4: 'Four', 5: 'Five', 6: 'Six', 7: 'Seven', 8: 'Eight', 9: 'Nine', 10: 'Ten', 11: 'Jack', 12: 'Queen', 13: 'King', 14: 'Ace' };
  const MANY = { 2: 'Twos', 3: 'Threes', 4: 'Fours', 5: 'Fives', 6: 'Sixes', 7: 'Sevens', 8: 'Eights', 9: 'Nines', 10: 'Tens', 11: 'Jacks', 12: 'Queens', 13: 'Kings', 14: 'Aces' };
  function handName(sc) {
    const cat = Math.floor(sc / CAT), k0 = Math.floor(sc / 50625) % 15, k1 = Math.floor(sc / 3375) % 15;
    switch (cat) {
      case 8: return k0 === 14 ? 'Royal flush' : 'Straight flush, ' + ONE[k0] + ' high';
      case 7: return 'Four ' + MANY[k0];
      case 6: return 'Full house, ' + MANY[k0] + ' full of ' + MANY[k1];
      case 5: return 'Flush, ' + ONE[k0] + ' high';
      case 4: return 'Straight, ' + ONE[k0] + ' high';
      case 3: return 'Three ' + MANY[k0];
      case 2: return 'Two pair, ' + MANY[k0] + ' and ' + MANY[k1];
      case 1: return 'Pair of ' + MANY[k0];
      default: return 'High card ' + ONE[k0];
    }
  }

  // ---- equity against ranges -------------------------------------------------------------------
  // An opponent is { width, post }: width = the top share of starting hands their preflop play
  // suggests; post = what they did after the flop. Each postflop action keeps a sampled hand with a
  // probability by how well it hits the board AT THAT STREET — bets come from strong hands and
  // draws (some bluffs), checks lean weaker. So a range narrows the way a thinking player's read does.
  // { fixed: [card, card] } is an opponent whose cards are known (face-up teaching tables).
  const ACCEPT = { bet: [0.22, 0.55, 0.92, 1], call: [0.12, 0.8, 1, 1], check: [1, 0.95, 0.7, 0.4] };
  // Every hand an opponent could hold here, each with the probability that their actions fit it: the
  // chart they played (or the top `width` of hands), minus the cards we can see, weighted by ACCEPT for
  // each street they bet, called or checked. Built once per equity run; sampled directly.
  function candidates(o, board, base) {
    const C = combos(), pick = o.set ? C.filter(c => o.set.has(cls(c.x, c.y))) : C.slice(0, Math.max(6, Math.min(1326, Math.round((o.width || 1) * 1326))));
    const list = [], cum = []; let total = 0;
    for (const c of pick) {
      if (base[c.a] || base[c.b]) continue;
      let w = 1; for (const a of (o.post || [])) w *= ACCEPT[a.kind][tierOn([c.x, c.y], board.slice(0, a.n))];
      if (w <= 0) continue;
      total += w; list.push(c); cum.push(total);
    }
    if (!list.length) { for (const c of C) if (!base[c.a] && !base[c.b]) { total += 1; list.push(c); cum.push(total); } }   // nothing fits (shouldn't happen): any hand
    return { list, cum, total };
  }
  function sampleFrom(cand, dead, rng) {
    for (let t = 0; t < 12; t++) {
      const r = rng() * cand.total; let lo = 0, hi = cand.cum.length - 1;
      while (lo < hi) { const mid = (lo + hi) >> 1; if (cand.cum[mid] < r) lo = mid + 1; else hi = mid; }
      const c = cand.list[lo]; if (!dead[c.a] && !dead[c.b]) return c;
    }
    for (const c of cand.list) if (!dead[c.a] && !dead[c.b]) return c;   // the other opponents took the rest: first free one
    return null;
  }
  function equityVsRanges(hero, board, opps, trials, rng) {
    rng = rng || Math.random; trials = trials || 2500;
    if (!opps || !opps.length) return 100;
    const base = new Uint8Array(52); hero.concat(board).forEach(c => { base[cid(c)] = 1; });
    const cands = opps.map(o => o.fixed ? null : candidates(o, board, base));
    let won = 0;
    for (let t = 0; t < trials; t++) {
      const dead = base.slice(), hands = [];
      for (let k = 0; k < opps.length; k++) {
        const o = opps[k]; let c;
        if (o.fixed) { const x = o.fixed[0], y = o.fixed[1]; c = { a: cid(x), b: cid(y), x, y }; }
        else c = sampleFrom(cands[k], dead, rng);
        if (!c) { let id; do { id = Math.floor(rng() * 52); } while (dead[id]); const x = fromId(id); dead[id] = 1; let id2; do { id2 = Math.floor(rng() * 52); } while (dead[id2]); c = { a: id, b: id2, x, y: fromId(id2) }; }
        dead[c.a] = dead[c.b] = 1; hands.push([c.x, c.y]);
      }
      const full = board.slice();
      while (full.length < 5) { let id; do { id = Math.floor(rng() * 52); } while (dead[id]); dead[id] = 1; full.push(fromId(id)); }
      const hs = evalHand(hero.concat(full));
      let best = -1, ties = 0;
      for (const h of hands) { const v = evalHand(h.concat(full)); if (v > best) { best = v; ties = 0; } if (v === best) ties++; }
      if (hs > best) won += 1; else if (hs === best) won += 1 / (ties + 1);
    }
    return r1(won / trials * 100);
  }

  // ---- the table -------------------------------------------------------------------------------
  // The kinds of player you meet. widen: opens wider (+) or tighter (−) than the charts; call: calls
  // raises with extra hands; aggr: how often it bets its good hands; bluff: how often it bets weak ones;
  // sticky: calls with that much less equity than the price needs; limp: how often it just calls first
  // in; foldToAggr: needs that much more equity to call a bet; slowplay: how often it checks/calls a
  // very strong hand to trap.
  const STYLES = {
    tag: { label: 'tight-aggressive', widen: 0, call: 0, aggr: 0.75, bluff: 0.12, sticky: 0 },
    lag: { label: 'loose-aggressive', widen: 0.12, call: 0.05, aggr: 0.85, bluff: 0.22, sticky: 0.03 },
    nit: { label: 'nit (only premium hands)', widen: -0.06, call: -1, aggr: 0.45, bluff: 0.04, sticky: -0.04 },
    station: { label: 'calling station', widen: 0.05, call: 0.3, aggr: 0.3, bluff: 0.05, sticky: 0.14, limp: 0.5 },
    maniac: { label: 'maniac', widen: 0.36, call: 0.15, aggr: 0.95, bluff: 0.35, sticky: 0.06 },
    fish: { label: 'recreational (limps and calls)', widen: 0.2, call: 0.35, aggr: 0.25, bluff: 0.05, sticky: 0.1, limp: 0.8 },
    weaktight: { label: 'weak-tight (folds to pressure)', widen: -0.03, call: -1, aggr: 0.5, bluff: 0.05, sticky: -0.06, foldToAggr: 0.08 },
    trapper: { label: 'trapper (slow-plays big hands)', widen: 0, call: 0.05, aggr: 0.55, bluff: 0.08, sticky: 0.02, slowplay: 0.6 },
    shark: { label: 'shark (strong all-rounder)', widen: 0.02, call: 0, aggr: 0.8, bluff: 0.14, sticky: 0 },
  };
  // How each style plays, in a sentence — shown beside every explained bot move, so you learn to spot
  // the type and what to do against it.
  const STYLE_HOW = {
    tag: 'Plays few hands, and bets and raises the good ones hard. The solid winning style — respect its bets.',
    lag: 'Plays lots of hands and keeps up the pressure with bets and raises. Hard to read; you can call it down a little lighter.',
    nit: 'Only plays premium hands and rarely bluffs. When it bets or raises, believe it — and steal its blinds.',
    station: 'Calls far too often and rarely raises. Never bluff it; bet your good hands bigger, because it pays you off.',
    maniac: 'Raises and bets almost everything, often with nothing. Let it bluff into your strong hands; don’t try to push it off a hand.',
    fish: 'A recreational player: limps in and calls with too many hands, chasing draws. Bet your good hands for value.',
    weaktight: 'Plays tight and gives up when someone bets. Bluff it more; when it does fight back, it has a strong hand.',
    trapper: 'Checks and calls with its very best hands to trap you. When it suddenly raises late in a hand, slow down.',
    shark: 'A strong all-rounder that plays close to the right strategy — the toughest player at the table. Avoid big pots with it unless your hand is strong.',
  };
  // Skill: how often a player makes a random, unconsidered play instead of their normal one.
  const SKILL = { beginner: { name: 'beginner', err: 0.2 }, casual: { name: 'casual', err: 0.1 }, regular: { name: 'regular', err: 0.04 }, pro: { name: 'pro', err: 0 } };
  // Which players sit down, by the table's Opponents setting.
  const FIELDS = {
    mixed: { name: 'A mixed table (every type and level)', styles: Object.keys(STYLES), levels: ['beginner', 'casual', 'regular', 'pro'] },
    easy: { name: 'An easier table (beginners and casual players)', styles: ['fish', 'station', 'maniac', 'weaktight', 'nit', 'lag'], levels: ['beginner', 'casual'] },
    tough: { name: 'A tough table (regulars and pros)', styles: ['tag', 'lag', 'shark', 'trapper', 'nit'], levels: ['regular', 'pro'] },
    // tables of ONE type, to practise the adjustment the Reading lesson teaches — and score only that
    stations: { name: 'A table of calling stations — practise: value bet thin, never bluff', styles: ['station', 'fish'], levels: ['beginner', 'casual'], lesson: 'stations' },
    nits: { name: 'A table of nits — practise: steal their blinds, fold to their raises', styles: ['nit', 'weaktight'], levels: ['casual', 'regular'], lesson: 'nits' },
    maniacs: { name: 'A table of maniacs — practise: call down lighter, let them bluff', styles: ['maniac', 'lag'], levels: ['casual', 'regular'], lesson: 'maniacs' },
    pros: { name: 'A table of tight-aggressive pros — practise: tight, positional, no loose calls', styles: ['tag', 'shark'], levels: ['pro'], lesson: 'pros' },
  };
  const TABLE_LESSONS = {
    stations: { title: 'calling stations', good: 'value bet into a caller', bad: 'bluffed a player who calls too much' },
    nits: { title: 'nits', good: 'stole from players who only play premiums', bad: 'paid off a nit’s raise with a hand that’s behind' },
    maniacs: { title: 'maniacs', good: 'called the maniac down lighter', bad: 'folded to a maniac’s bet with enough to call' },
    pros: { title: 'pros', good: 'played tight and in position', bad: 'called a raise out of position with a weak hand' },
  };
  // Score one decision against the table's lesson (only on a one-type table). Returns +1, -1 or 0 with a note.
  function tableLessonScore(s, kind, E) {
    const F = FIELDS[opts.field || 'mixed'], L = F && F.lesson; if (!L) return null;
    const e = E == null ? null : E / 100, late = /^(CO|BTN|SB)$/.test(s.pos);
    if (L === 'stations' && s.street && s.toCall <= 0 && e != null) {
      const th = thresholds(s), d = draws(s.cards, s.board);
      if (kind === 'raise' && e < th.vt - 0.05 && d.outs < 8) return { v: -1, note: TABLE_LESSONS[L].bad };
      if (kind === 'raise' && e >= th.vt - 0.05) return { v: 1, note: TABLE_LESSONS[L].good };
    }
    if (L === 'nits' && !s.street) {
      if (s.raises === 0 && late && kind === 'raise') return { v: 1, note: TABLE_LESSONS[L].good };
      if (s.raises >= 1 && kind === 'call' && !chart('vs3betCall').has(s.k) && !chart('ipCallEarly').has(s.k)) return { v: -1, note: TABLE_LESSONS[L].bad };
      if (s.raises >= 1 && kind === 'fold') return { v: 1, note: 'folded to a nit’s raise' };
    }
    if (L === 'maniacs' && s.street && s.toCall > 0 && e != null) {
      const need = s.toCall / (s.pot + s.toCall);
      if (kind === 'call' && e >= need - 0.08) return { v: 1, note: TABLE_LESSONS[L].good };
      if (kind === 'fold' && e >= need) return { v: -1, note: TABLE_LESSONS[L].bad };
    }
    if (L === 'pros' && !s.street) {
      if (s.raises >= 1 && kind === 'call' && /^(SB|BB)$/.test(s.pos) && !chart('bbCallEarly').has(s.k)) return { v: -1, note: TABLE_LESSONS[L].bad };
      if (s.raises === 0 && kind === 'raise' && chart('rfi.' + s.pos) && chart('rfi.' + s.pos).has(s.k)) return { v: 1, note: TABLE_LESSONS[L].good };
    }
    return null;
  }
  function tableLessonLine() {
    const F = FIELDS[opts.field || 'mixed']; if (!F || !F.lesson) return '';
    const t = (stats.tableLesson || {})[F.lesson]; if (!t || !(t.good + t.bad)) return '';
    return TABLE_LESSONS[F.lesson].title + ': ' + t.good + ' ✓ · ' + t.bad + ' ✗' + (t.last ? ' — last: ' + t.last : '');
  }
  const BOTS = ['Viktor', 'Mia', 'Old Pete', 'Dougie', 'Zara', 'Kenji', 'Rosa', 'Sal', 'Priya', 'Tomasz', 'Gloria', 'Ade', 'Hugo', 'Lena'];
  function newGame(rng, field, n) {
    n = n || NSEATS;
    const F = FIELDS[field] || FIELDS.mixed;
    const shuffle = a => { a = a.slice(); for (let i = a.length - 1; i > 0; i--) { const j = Math.floor(rng() * (i + 1)); const t = a[i]; a[i] = a[j]; a[j] = t; } return a; };
    const names = shuffle(BOTS), styles = shuffle(F.styles);
    const bots = Array.from({ length: n - 1 }, (_, k) => k).map(k => {
      const style = styles[k % styles.length];
      // a shark is always good; a recreational player is never a pro
      const level = style === 'shark' ? 'pro' : style === 'fish' ? F.levels[0] : F.levels[Math.floor(rng() * F.levels.length)];
      return { name: names[k], style, level, isHero: false };
    });
    return { players: [{ name: 'You', style: null, isHero: true }].concat(bots), button: Math.floor(rng() * n), handNo: 0, gid: Math.floor(rng() * 1e9).toString(36) };
  }
  const botLabel = p => STYLES[p.style].label + (p.level && SKILL[p.level] ? ' · ' + SKILL[p.level].name : '');
  // g.dead = the big-blind ante: dead money in the pot that belongs to no one's bet.
  const potTotal = g => g.players.reduce((a, p) => a + p.total, 0) + (g.dead || 0);
  const posOf = (g, i) => { if (g.pos) return g.pos[i]; const n = g.players.length; return (POS_BY_N[n] || POS)[(i - g.button + n) % n]; };
  const actors = g => g.players.filter(p => !p.folded && !p.allin);
  // Position names by how many are still in, counted from the button. Heads-up the button posts the
  // small blind and acts first before the flop, last after it.
  const POS_BY_N = { 8: POS, 7: ['BTN', 'SB', 'BB', 'UTG', 'LJ', 'HJ', 'CO'], 6: ['BTN', 'SB', 'BB', 'LJ', 'HJ', 'CO'], 5: ['BTN', 'SB', 'BB', 'HJ', 'CO'], 4: ['BTN', 'SB', 'BB', 'CO'], 3: ['BTN', 'SB', 'BB'], 2: ['BTN', 'BB'] };
  // A hand. Cash: everyone back to 100bb. Tournament (g.tour): stacks carry over in chips, read in
  // big blinds at the current level; busted seats sit out; the big blind also posts a 1bb ante.
  // Amounts inside a hand are always in big blinds.
  function newHand(g, rng) {
    const T = g.tour, alive = i => !T || T.chips[i] > 0;
    g.handNo++;
    const NS = g.players.length;
    let b = g.button; for (let k = 0; k < NS; k++) { b = (b + 1) % NS; if (alive(b)) break; }
    // Going heads-up (TDA / PokerStars Live): the player who last had the big blind takes the button,
    // so nobody posts the big blind twice in a row.
    const nAlive = g.players.filter((p, i) => alive(i)).length;
    if (T && nAlive === 2 && (g.prevAlive || NS) > 2 && g.lastBB != null && alive(g.lastBB)) b = g.lastBB;
    g.button = b;
    const order = []; for (let k = 0; k < NS; k++) { const j = (b + k) % NS; if (alive(j)) order.push(j); }
    const n = order.length, names = POS_BY_N[n] || POS;
    g.pos = new Array(NS).fill('');
    order.forEach((j, k) => { g.pos[j] = names[k]; });
    g.preOrder = n === 2 ? order.slice() : order.slice(3).concat(order.slice(0, 3));   // who acts first before the flop
    const unit = T ? T.levels[T.level] : 1, deck = shuffled(rng);
    g.players.forEach((p, i) => {
      const out = !alive(i);
      Object.assign(p, { stack: out ? 0 : (T ? T.chips[i] / unit : (g.depth || 100)), cards: out ? [] : [deck.pop(), deck.pop()], bet: 0, total: 0, folded: out, out, allin: false, acted: false, actedAt: 0, rangeW: 1, rangeSet: null, post: [] });
    g.lastRaiser = -1;
    });
    g.startStacks = g.players.map(p => p.stack);
    Object.assign(g, { deck, board: [], street: 0, curBet: 0, minRaise: 1, raises: 0, openerSeat: -1, log: [], acts: [], watchLog: [], over: false, result: null, _done: false, dead: 0 });
    const sbSeat = n === 2 ? order[0] : order[1], bbSeat = n === 2 ? order[1] : order[2];
    g.bbSeat = bbSeat; g.lastBB = bbSeat; g.prevAlive = n; g.unit = unit;
    const post = (i, amt, ante) => {
      const p = g.players[i], a = Math.min(amt, p.stack);
      p.stack -= a; if (ante) g.dead += a; else { p.bet += a; p.total += a; }
      if (p.stack <= 1e-9) { p.stack = 0; p.allin = true; }
      g.log.push({ st: 0, i, pos: posOf(g, i), txt: 'posts ' + (ante ? 'the ante ' : '') + bbs(a), kind: 'post' });
    };
    if (T) post(bbSeat, 1, true);
    post(sbSeat, 0.5); post(bbSeat, 1);
    g.curBet = 1;
    g.toAct = nextActor(g, bbSeat);
    if (g.toAct < 0) { while (g.street < 3) nextStreet(g); finish(g); }   // everyone all-in from the blinds
  }
  function legal(g, i) {
    const p = g.players[i];
    const toCall = Math.max(0, Math.min(g.curBet - p.bet, p.stack));
    const maxTo = p.bet + p.stack;
    const reopened = !p.acted || g.curBet - (p.actedAt || 0) >= g.minRaise - 1e-9;
    return { toCall, maxTo, minTo: Math.min(g.curBet + g.minRaise, maxTo), canRaise: maxTo > g.curBet && p.stack > toCall && reopened, pot: potTotal(g) };
  }
  // What the table can SEE of a player's range, set as they act (see sampleHand).
  // The hands a preflop action is played with, as the CHART has them (not "the best N%" — a 3-bet
  // chart holds A5s and A4s and not JJ; a top-N list has it the other way round). Returns a Set of hand
  // classes, or null where no chart applies (a limp, a small-blind call), in which case a width is used.
  function rangeSetFor(g, i, kind) {
    const pos = posOf(g, i), opener = g.openerSeat >= 0 ? posOf(g, g.openerSeat) : '', grp = /^(CO|BTN|SB)$/.test(opener) ? 'Late' : 'Early';
    const opened = g.openerSeat === i, limpers = g.log.some(l => l.st === 0 && l.kind === 'call');
    if (kind === 'raise') {
      if (g.raises === 0) return pos === 'BB' ? chart('isoLimp') : (limpers ? chart('rfi.' + pos) : chart('rfi.' + pos));
      if (g.raises === 1) return chart((pos === 'BB' ? 'bb3' : pos === 'SB' ? 'sb3' : 'ip3') + grp);
      if (g.raises === 2) return chart(opened ? 'vs3bet4' : 'cold4');
      return chart('jam4');
    }
    if (kind === 'call') {
      if (g.raises === 0) return null;                                              // a limp: wide, no chart
      if (g.raises === 1) return pos === 'BB' ? chart('bbCall' + grp) : pos === 'SB' ? null : chart('ipCall' + grp);
      if (g.raises === 2) return chart(opened ? 'vs3betCall' : 'coldCall');
      return chart('call4');
    }
    return null;
  }
  const setWidth = set => { let n = 0; for (const k of set) n += combosOf(k); return n / 1326; };
  function preRole(g, i, kind) {
    const p = g.players[i], pos = posOf(g, i); let w;
    if (kind === 'raise') w = g.raises === 0 ? (pos === 'BB' ? 0.3 : chartWidth('rfi.' + pos)) : g.raises === 1 ? 0.07 : g.raises === 2 ? 0.035 : 0.025;
    else if (kind === 'call') w = g.raises === 0 ? 0.6 : g.raises === 1 ? (pos === 'BB' ? 0.4 : 0.2) : g.raises === 2 ? 0.1 : 0.03;
    else return;
    const set = rangeSetFor(g, i, kind);
    if (set && set.size) { p.rangeSet = set; w = Math.min(w, setWidth(set)); } else if (kind === 'raise') p.rangeSet = null;
    p.rangeW = Math.min(p.rangeW, w);
  }
  function act(g, i, a) {
    if (g.over || g.toAct !== i) throw new Error('not seat ' + i + "'s turn");
    const p = g.players[i], L = legal(g, i), st = g.street;
    let kind = a.type, txt = '';
    if (kind === 'check' && L.toCall > 0) throw new Error('cannot check facing a bet');
    if (kind === 'raise' && !L.canRaise) kind = 'call';
    let finalTo = 0;
    if (kind === 'raise') {
      let to = Math.max(L.minTo, Math.min(L.maxTo, half(a.to || 0)));
      if (L.maxTo - to < 0.5) to = L.maxTo;                    // within half a blind of all-in: all-in
      if (to <= g.curBet) kind = 'call';
      else {
        finalTo = to;
        const add = to - p.bet, was = g.curBet, full = to - was >= g.minRaise - 1e-9;
        if (st === 0) preRole(g, i, 'raise'); else p.post.push({ kind: 'bet', n: g.board.length });
        p.stack -= add; p.bet = to; p.total += add;
        if (to - was >= g.minRaise) g.minRaise = to - was;
        g.curBet = to; g.raises++;
        if (st === 0 && g.openerSeat < 0) g.openerSeat = i;
        g.lastRaiser = i;
        // only a full raise reopens the betting for players who have already acted (a short all-in
        // still makes them call or fold the extra — nextActor sees their bet is below the new one)
        if (full) g.players.forEach((q, j) => { if (j !== i && !q.folded && !q.allin) q.acted = false; });
        txt = (p.stack <= 0 ? 'all-in ' : (was === 0 ? 'bets ' : 'raises to ')) + bbs(to);
      }
    }
    if (kind === 'call') {
      const add = Math.min(g.curBet - p.bet, p.stack);
      if (add <= 0) kind = 'check';
      else {
        if (st === 0) preRole(g, i, 'call'); else p.post.push({ kind: 'call', n: g.board.length });
        p.stack -= add; p.bet += add; p.total += add;
        txt = 'calls ' + bbs(add) + (p.stack <= 0 ? ' (all-in)' : '');
      }
    }
    if (kind === 'check') { txt = 'checks'; if (st > 0) p.post.push({ kind: 'check', n: g.board.length }); }
    if (kind === 'fold') { p.folded = true; txt = 'folds'; }
    if (p.stack <= 1e-9) { p.stack = 0; p.allin = true; }
    p.acted = true; p.actedAt = g.curBet;
    g.log.push({ st, i, pos: posOf(g, i), txt, kind });
    // The hand's action list, exactly as played: with the shuffle's seed it rebuilds the hand anywhere
    // (the web friends' table sends only this).
    (g.acts || (g.acts = [])).push([i, kind, finalTo]);
    advance(g);
    return kind;
  }
  function nextActor(g, from) {
    const NS = g.players.length;
    for (let k = 1; k <= NS; k++) {
      const j = (from + k) % NS, p = g.players[j];
      if (!p.folded && !p.allin && (!p.acted || p.bet < g.curBet)) return j;
    }
    return -1;
  }
  function nextStreet(g) {
    g.street++;
    g.players.forEach(p => { p.bet = 0; p.acted = false; p.actedAt = 0; });
    g.curBet = 0; g.minRaise = 1; g.raises = 0;
    g.deck.pop();                                               // burn
    for (let k = g.street === 1 ? 3 : 1; k > 0; k--) g.board.push(g.deck.pop());
    g.toAct = nextActor(g, g.button);
  }
  function advance(g) {
    if (g.players.filter(p => !p.folded).length === 1) return finish(g);
    const nx = nextActor(g, g.toAct);
    if (nx >= 0) { g.toAct = nx; return; }
    if (g.street === 3) return finish(g);
    nextStreet(g);
    if (actors(g).length > 1) return;
    while (g.street < 3) nextStreet(g);                         // all-in: run the board out
    finish(g);
  }
  // Pots are built level by level from what each player put in, so an all-in player only wins what
  // they could match; an uncalled excess comes back to whoever bet it.
  function settle(g) {
    const live = g.players.map((p, i) => ({ p, i })).filter(x => !x.p.folded);
    const wins = [];
    if (live.length === 1) {
      const amt = potTotal(g); live[0].p.stack += amt;
      wins.push({ i: live[0].i, amt, name: '' });
      return { wins, showdown: false };
    }
    const sc = {}; live.forEach(x => { sc[x.i] = evalHand(x.p.cards.concat(g.board)); });
    const levels = Array.from(new Set(live.map(x => x.p.total))).sort((a, b) => a - b);
    let prev = 0;
    for (const lv of levels) {
      let amt = prev === 0 ? (g.dead || 0) : 0;                 // the ante belongs to the main pot
      g.players.forEach(p => { amt += Math.min(p.total, lv) - Math.min(p.total, prev); });
      const elig = live.filter(x => x.p.total >= lv);
      const best = Math.max.apply(null, elig.map(x => sc[x.i]));
      const ws = elig.filter(x => sc[x.i] === best);
      const credit = (w, share) => {
        w.p.stack += share;
        const have = wins.find(z => z.i === w.i);
        if (have) have.amt += share; else wins.push({ i: w.i, amt: share, name: handName(sc[w.i]) });
      };
      if (g.tour && g.unit && ws.length > 1) {
        // whole chips; any odd chip goes to the first winner clockwise from the button (TDA / PokerStars Live)
        const chips = Math.round(amt * g.unit), base = Math.floor(chips / ws.length);
        let odd = chips - base * ws.length;
        ws.slice().sort((a, b) => ((a.i - g.button - 1 + 2 * g.players.length) % g.players.length) - ((b.i - g.button - 1 + 2 * g.players.length) % g.players.length))
          .forEach(w => { const c = base + (odd > 0 ? 1 : 0); if (odd > 0) odd--; credit(w, c / g.unit); });
      } else for (const w of ws) credit(w, amt / ws.length);
      prev = lv;
    }
    return { wins, showdown: true, scores: sc };
  }
  function finish(g) { g.result = settle(g); g.over = true; g.toAct = -1; if (g.tour) tourAfterHand(g); }

  // ---- tournaments ------------------------------------------------------------------------------
  // Sit-and-go style: everyone starts with the same chips, blinds rise every few hands, the big blind
  // posts a 1bb ante (the WSOP standard), players are knocked out, the table shrinks to heads-up.
  // Prizes are paid by finishing place; prize equity along the way is ICM (pushfold.js).
  const LEVELS = [100, 150, 200, 250, 300, 400, 500, 600, 800, 1000, 1200, 1500, 2000, 2500, 3000, 4000, 5000, 6000, 8000, 10000, 12000, 15000, 20000, 25000, 30000, 40000, 50000, 60000, 80000, 100000];
  const PAYOUTS = { top3: { name: 'Top 3 paid — 50/30/20', split: [0.5, 0.3, 0.2] }, top2: { name: 'Top 2 paid — 65/35', split: [0.65, 0.35] }, wta: { name: 'Winner takes all', split: [1] } };
  function newTournament(g, opts) {
    opts = opts || {};
    const start = opts.startBB || 40, pool = g.players.length * (opts.buyIn || 100), split = (PAYOUTS[opts.payouts] || PAYOUTS.top3).split;
    g.tour = { level: 0, handsAt: 0, perLevel: opts.perLevel || 6, levels: LEVELS, startBB: start, startChips: start * LEVELS[0],
      chips: g.players.map(() => start * LEVELS[0]), place: g.players.map(() => 0), prize: g.players.map(() => 0),
      payouts: split.map(f => Math.round(f * pool)), payoutKey: opts.payouts || 'top3', pool, done: false, levelUp: false };
    g.handNo = 0; g.gid = 't' + Date.now().toString(36);
    return g.tour;
  }
  function tourAfterHand(g) {
    const T = g.tour, unit = T.levels[T.level];
    const before = g.players.map((p, i) => i).filter(i => !g.players[i].out);
    g.players.forEach((p, i) => { if (!p.out) T.chips[i] = Math.round(p.stack * unit); });
    // keep the chip total exact (rounding a split pot can leave a chip or two over)
    const drift = g.players.length * T.startChips - T.chips.reduce((a, c) => a + c, 0);
    if (drift) { const big = before.reduce((a, i) => T.chips[i] > T.chips[a] ? i : a, before[0]); T.chips[big] += drift; }
    // knocked out this hand: the smaller starting stack takes the lower place
    const busted = before.filter(i => T.chips[i] <= 0).sort((a, b) => g.startStacks[a] - g.startStacks[b]);
    let place = before.length;
    for (const i of busted) { T.place[i] = place; T.prize[i] = T.payouts[place - 1] || 0; place--; }
    const left = before.filter(i => T.chips[i] > 0);
    if (left.length === 1) { T.place[left[0]] = 1; T.prize[left[0]] = T.payouts[0] || 0; T.done = true; }
    T.levelUp = false;
    if (++T.handsAt >= T.perLevel && !T.done) { T.level = Math.min(T.level + 1, T.levels.length - 1); T.handsAt = 0; T.levelUp = true; }
  }
  // Each player's prize equity right now (ICM), by seat.
  function tourIcm(g) {
    const T = g.tour, seats = g.players.map((p, i) => i).filter(i => T.chips[i] > 0);
    const eq = PushFold.icm(seats.map(i => T.chips[i]), T.payouts.slice(0, seats.length));
    const out = g.players.map((p, i) => T.place[i] ? T.prize[i] : 0);
    seats.forEach((s, k) => { out[s] = eq[k]; });
    return out;
  }
  // The short-stack decision in front of seat i, if there is one: shoving first in (≤20bb effective),
  // or facing a single all-in with nobody in between.
  const effStack = (g, i) => {
    const me = g.players[i].stack + g.players[i].bet;
    const others = g.players.filter((q, j) => j !== i && !q.folded).map(q => q.stack + q.bet);
    return others.length ? Math.min(me, Math.max.apply(null, others)) : me;
  };
  function shortSpot(g, i) {
    if (g.street !== 0 || g.toAct !== i) return null;
    const S = effStack(g, i);
    const after = g.preOrder.slice(g.preOrder.indexOf(i) + 1).filter(j => !g.players[j].folded);
    if (g.raises === 0 && posOf(g, i) !== 'BB' && S <= PushFold.MAX_S && !g.log.some(l => l.kind === 'call')) return { type: 'shove', m: after.length, S, order: after };
    if (g.raises === 1 && g.openerSeat >= 0 && g.players[g.openerSeat].allin) {
      const p = g.openerSeat, Sp = g.players[p].bet;
      const calledSince = g.log.some(l => l.kind === 'call' && l.st === 0);
      if (!calledSince && Sp <= PushFold.MAX_S + 0.5) return { type: 'call', pusher: p, mp: g.preOrder.length - 1 - g.preOrder.indexOf(p), S: Sp };
    }
    return null;
  }
  // The table as the ICM maths needs it: only the players still in, in bb, from seat i's chair.
  function pfTable(g, i, order) {
    const seats = g.players.map((p, k) => k).filter(k => !g.players[k].out), at = s => seats.indexOf(s);
    return {
      seats,
      t: { stacks: seats.map(s => g.players[s].stack), posted: seats.map(s => g.players[s].bet), dead: g.dead || 0,
        payouts: g.tour.payouts.slice(0, seats.length), hero: at(i), order: (order || []).map(at), bb: at(g.bbSeat) },
    };
  }

  // ---- the bots --------------------------------------------------------------------------------
  function sized(g, i, to) {
    const p = g.players[i], max = p.bet + p.stack; to = half(to);
    return { type: 'raise', to: to >= max * 0.75 ? max : to };
  }
  const threeBetTo = (g, i) => g.curBet * (/^(SB|BB)$/.test(posOf(g, i)) ? 4 : 3);
  const openTo = (g, i) => {
    const limpers = g.players.filter((q, j) => j !== i && q.acted && !q.folded && q.bet === g.curBet && posOf(g, j) !== 'BB').length;
    return (posOf(g, i) === 'SB' ? 3 : 2.5) + limpers * 1.5;
  };
  // Every bot decision carries a plain-English reason (d.why), shown when you watch a hand you've
  // folded out of. Building a reason never draws from rng, so explained and silent play are identical.
  const why = (d, text) => { d.why = text; return d; };
  const pctW = v => r1(v * 100) + '%';
  const styleName = k => STYLES[k] ? STYLES[k].label.replace(/ \(.*\)$/, '') : 'player';   // "weak-tight (folds to pressure)" → "weak-tight"
  // "a pair of Aces", "two pair, Kings and Sevens", "just Queen high"
  const madeHand = (cards, board) => {
    const n = handName(evalHand(cards.concat(board)));
    if (/^High card/.test(n)) return 'just ' + n.replace(/^High card,?\s*/, '') + ' high';
    if (/^(Pair|Straight|Flush|Full house|Royal flush)/.test(n)) return 'a ' + n.charAt(0).toLowerCase() + n.slice(1);
    return n.charAt(0).toLowerCase() + n.slice(1);
  };
  // The best players don't play one fixed style. The shark changes gear about every 10 hands (tighter,
  // then looser) so it can't be read; and the shark and pro-level tight/loose-aggressive players pick
  // their bluffs — against players who fold, heads-up, in position, on a scary card — and don't bluff
  // players who never fold. Gear comes from the hand number, not rng.
  const isAdaptive = p => p.style === 'shark' || (p.level === 'pro' && (p.style === 'tag' || p.style === 'lag'));
  function gearOf(g, i) {
    const p = g.players[i];
    if (p.style !== 'shark') return { widen: 0, loose: false, note: '' };
    const loose = Math.floor(((g.handNo || 0) + i * 3) / 10) % 2 === 1;
    return loose ? { widen: 0.08, loose: true, note: ' It’s in a loose gear right now — the best players switch gears so they can’t be read.' }
      : { widen: -0.03, loose: false, note: ' It’s in a tight gear right now — the best players switch gears so they can’t be read.' };
  }
  // How good a moment this is to bluff, and why: a multiplier on the bot's bluffing, plus the reasons.
  function bluffMoment(g, i) {
    const p = g.players[i];
    if (!isAdaptive(p)) return { x: 1, why: [] };
    const opp = g.players.filter((q, j) => j !== i && !q.folded);
    const why = []; let x = 1;
    const callers = opp.filter(q => q.style === 'station' || q.style === 'fish');
    if (callers.length) return { x: 0.15, why: ['it won’t bluff ' + (callers.length === 1 ? callers[0].name + ', a player who calls too much' : 'players who call too much')] };
    if (opp.length && opp.every(q => q.style === 'nit' || q.style === 'weaktight')) { x *= 2.2; why.push((opp.length === 1 ? opp[0].name + ' folds' : 'they fold') + ' too easily when someone bets'); }
    if (opp.length === 1) { x *= 1.3; why.push('only one opponent to get past'); } else if (opp.length >= 3) { x *= 0.3; }
    const order = []; for (let k = 1; k <= g.players.length; k++) order.push((g.button + k) % g.players.length);
    const live = order.filter(j => !g.players[j].folded);
    if (live[live.length - 1] === i) { x *= 1.3; why.push('it acts last, so it saw them check'); }
    if (g.street >= 2) {
      const c = g.board[g.board.length - 1], before = g.board.slice(0, -1);
      const suits = {}; g.board.forEach(b => { suits[b.s] = (suits[b.s] || 0) + 1; });
      if (c.r >= 13 && before.every(b => b.r < c.r)) { x *= 1.8; why.push('the ' + (c.r === 14 ? 'Ace' : 'King') + ' that just came is a scary card it can claim to have'); }
      else if (suits[c.s] === 3) { x *= 1.6; why.push('the last card put three of a suit on the board, so it can represent a flush'); }
    }
    return { x, why };
  }
  function botPreflop(g, i, rng) {
    const p = g.players[i], S = STYLES[p.style], k = cls(p.cards[0], p.cards[1]), P = pct()[k], pos = posOf(g, i), L = legal(g, i);
    const hw = handWords(k) + ' (' + k + ')', st = styleName(p.style), gear = gearOf(g, i), widen = S.widen + gear.widen;
    const light = rng() < 0.07 && (S.bluff >= 0.15 || gear.loose);   // the occasional light play from the loose, aggressive styles
    // Tournament short stacks play push/fold from the equilibrium tables. Loose styles shove as if
    // shorter (wider), nits as if deeper; calling stations and maniacs call on chips alone, the
    // others respect ICM — so there is something to exploit either way.
    const sp = shortSpot(g, i);
    if (sp && sp.type === 'shove') {
      const lean = S.widen >= 0.12 ? 1.35 : S.widen < 0 ? 0.75 : 1, go = PushFold.inPush(k, Math.max(1, sp.m), sp.S / lean);
      return why(go ? { type: 'raise', to: p.bet + p.stack } : { type: 'fold' }, 'Short stack: ' + r1(sp.S) + ' big blinds, so it’s all-in or fold. ' + hw
        + (go ? ' is in the all-in range from this seat, with ' + sp.m + ' player' + (sp.m === 1 ? '' : 's') + ' still to act.' : ' is not in the all-in range from this seat, so it folds.')
        + (lean > 1 ? ' As a loose player it shoves more hands than the chart says.' : lean < 1 ? ' As a tight player it shoves fewer hands than the chart says.' : ''));
    }
    if (sp && sp.type === 'call' && !g.tour) {                                   // cash: chips only, from the equilibrium call charts
      const ok = PushFold.inCall(k, Math.max(1, sp.mp), 1, Math.max(1, Math.min(PushFold.MAX_S, Math.round(sp.S)))) || (S.call >= 0.15 && P <= 0.12);
      return why(ok ? { type: 'call' } : { type: 'fold' }, 'Facing an all-in of ' + r1(sp.S) + ' big blinds. ' + hw + (ok ? ' is strong enough to call it.' : ' isn’t strong enough to call an all-in — it folds.'));
    }
    if (sp && sp.type === 'call') {
      const tb = pfTable(g, i, []);
      const r = PushFold.callSpot(tb.t, k, tb.seats.indexOf(sp.pusher), Math.max(1, sp.mp));
      const need = (S.call >= 0.15 ? r.needChips : r.needIcm) - S.sticky, ok = r.eq >= need;
      return why(ok ? { type: 'call' } : { type: 'fold' }, 'Facing an all-in. Against the hands that player shoves, ' + hw + ' wins about ' + pctW(r.eq) + ' of the time; it needs ' + pctW(need)
        + (S.call >= 0.15 ? ' (it only counts chips and ignores the prize-money risk — a loose caller)' : ' (counting the prize-money risk)') + '. ' + (ok ? 'Enough, so it calls.' : 'Not enough, so it folds.'));
    }
    if (g.raises === 0) {
      if (L.toCall === 0) return P <= 0.08 ? why(sized(g, i, 4), 'Nobody raised, only called, and ' + hw + ' is one of the best ' + pctW(P) + ' of hands — it raises to make the callers pay.')
        : why({ type: 'check' }, 'It’s the big blind and nobody raised, so it sees the flop for free with ' + hw + '.');   // big blind vs a limp
      const w = chartWidth('rfi.' + pos);
      const open = widen < 0 ? P <= w + widen : (chart('rfi.' + pos).has(k) || P <= w + widen);
      const top = hw + ' is ' + (P <= 0.5 ? 'one of the best ' + pctW(P) + ' of hands' : strengthWord(P) + ' (ranked #' + (PK_HAND_ORDER.indexOf(k) + 1) + ' of 169)') + '; from the ' + (POS_FULL[pos] || pos) + ' seat, good players raise the best ' + pctW(w) + '.';
      if (S.limp && rng() < S.limp && (open ? rng() < 0.8 : P <= 0.7)) return why({ type: 'call' }, 'It just calls (limps) instead of raising — typical of a ' + st + ' player. ' + top + ' Limping is a leak: it wins nothing straight away and lets everyone in cheaply.');   // mostly just calls, even with good hands
      if (open) return why(sized(g, i, openTo(g, i)), 'Everyone folded to it. ' + top + (chart('rfi.' + pos).has(k) || P <= w ? ' So it raises.' : ' A ' + st + ' player raises more hands than that, and this one is in its wider range.') + gear.note);
      if (light) return why(sized(g, i, openTo(g, i)), 'A bluff raise. ' + top + (gear.loose ? gear.note : ' Loose, aggressive players mix in some weak hands to steal the blinds.'));
      return why({ type: 'fold' }, 'Everyone folded to it. ' + top + ' Not good enough, so it folds.' + gear.note);
    }
    if (g.raises === 1) {
      const grp = /^(CO|BTN|SB)$/.test(posOf(g, g.openerSeat)) ? 'Late' : 'Early';
      const who = pos === 'BB' ? 'bb' : pos === 'SB' ? 'sb' : 'ip', opener = POS_FULL[posOf(g, g.openerSeat)] || 'raiser';
      const three = chart(who + '3' + grp).has(k);
      if (three || P <= S.widen * 0.25 || light) return why(sized(g, i, threeBetTo(g, i)), three ? hw + ' is strong enough to re-raise (3-bet) a raise from the ' + opener + '.'
        : 'A light re-raise (3-bet) with ' + hw + ' — ' + (light ? 'a bluff, to make the ' + opener + ' fold.' : 'a ' + st + ' player re-raises far more hands than the chart.'));
      const cs = who === 'sb' ? null : chart(who + 'Call' + grp);
      const call = S.call < 0 ? !!(cs && cs.has(k) && P <= 0.14) : (!!(cs && cs.has(k)) || P <= S.call + (who === 'bb' ? 0.12 : 0));
      if (call) return why({ type: 'call' }, 'Calls the ' + opener + '’s raise: ' + hw + (cs && cs.has(k) ? ' plays well enough after the flop to call, but isn’t strong enough to re-raise.' : ' isn’t really good enough, but a ' + st + ' player calls too often.')
        + (who === 'bb' ? ' In the big blind it already has 1 big blind in, so calling costs less.' : ''));
      return why({ type: 'fold' }, 'Folds to the ' + opener + '’s raise: ' + hw + ' isn’t strong enough' + (grp === 'Early' ? ' — a raise from an early seat usually means a strong hand.' : '.'));
    }
    if (g.raises === 2) {
      const opened = g.openerSeat === i;
      if (chart(opened ? 'vs3bet4' : 'cold4').has(k) || (S.widen >= 0.3 && P <= 0.05)) return why(sized(g, i, g.curBet * 2.3), 'Raises again (a 4-bet) with ' + hw + ' — after a raise and a re-raise, only the very best hands keep raising.');
      if (chart(opened ? 'vs3betCall' : 'coldCall').has(k) || P <= S.call * 0.3) return why({ type: 'call' }, 'Calls the re-raise with ' + hw + ' — good enough to continue, not to raise again.');
      return why({ type: 'fold' }, 'Folds to the re-raise: ' + hw + ' isn’t strong enough after two raises.');
    }
    if (L.toCall >= p.stack || g.curBet >= 0.5 * (p.bet + p.stack)) return (chart('callJam').has(k) || P <= S.widen * 0.12) ? why({ type: 'call' }, 'Calls for most of its chips with ' + hw + ' — one of the few hands strong enough.') : why({ type: 'fold' }, 'Folds: ' + hw + ' isn’t strong enough to risk most of its chips after so many raises.');
    if (chart('jam4').has(k)) return why({ type: 'raise', to: p.bet + p.stack }, 'Goes all-in with ' + hw + ' — a top hand.');
    if (chart('call4').has(k)) return why({ type: 'call' }, 'Calls with ' + hw + ' — strong, but not strong enough to go all-in.');
    return why({ type: 'fold' }, 'Folds ' + hw + ' — after three raises only the very best hands continue.');
  }
  function botPostflop(g, i, rng) {
    const p = g.players[i], S = STYLES[p.style], L = legal(g, i);
    const opps = g.players.filter((q, j) => j !== i && !q.folded).map(q => ({ width: q.rangeW, set: q.rangeSet, post: q.post }));
    const e = equityVsRanges(p.cards, g.board, opps, 600, rng) / 100;
    const n = opps.length, vt = n === 1 ? 0.58 : n === 2 ? 0.44 : 0.36;
    const d = draws(p.cards, g.board), drawy = d.outs >= 8 && g.street < 3;
    const trap = S.slowplay && e >= 0.8 && g.street < 3 && rng() < S.slowplay;
    const bm = bluffMoment(g, i), adapt = isAdaptive(p);
    const others = g.players.filter((q, j) => j !== i && !q.folded);
    const vsCallers = adapt && others.some(q => q.style === 'station' || q.style === 'fish');
    const vsManiac = adapt && others.some(q => q.style === 'maniac');
    const vtE = vt - (vsCallers ? 0.08 : 0);                                       // thinner value against players who call too much
    const made = madeHand(p.cards, g.board), E = Math.round(e * 100) + '%', st = styleName(p.style), them = n === 1 ? 'the other player probably holds' : 'the other ' + n + ' players probably hold';
    const odds = 'it reckons it wins about ' + E + ' against what ' + them + (drawy ? ', counting its draw' : '');
    if (L.toCall === 0) {
      if (trap) return why({ type: 'check' }, 'Checks with ' + made + ' — very strong (' + odds + '), so it slow-plays: a ' + st + ' player hopes someone bets into it.');
      if (e >= vtE && rng() < S.aggr) return why(sized(g, i, Math.max(1, L.pot * (e > 0.8 ? 0.75 : 0.5) * (S.widen >= 0.3 ? 1.4 : 1))), 'Bets for value with ' + made + ': ' + odds + ' — ahead often enough to want to be called.'
        + (e > 0.8 ? ' Very strong, so a bigger bet.' : '') + (S.widen >= 0.3 ? ' Maniacs bet extra big.' : '')
        + (vsCallers && e < vt ? ' This is a thin value bet: a good player bets weaker hands against someone who calls too much, because worse hands will pay.' : ''));
      if (rng() < S.bluff * bm.x * (drawy ? 2.2 : 1) * (n === 1 ? 1 : 0.4)) return why(sized(g, i, Math.max(1, L.pot * 0.5)), (drawy ? 'A semi-bluff: ' : 'A bluff: ') + 'only ' + made + ', and ' + odds + '.'
        + (drawy ? ' It bets to win the pot now, and can still hit its draw if called.' : ' It bets hoping better hands fold') + (drawy ? '' : (bm.why.length ? '.' : S.bluff >= 0.2 ? ' — a ' + st + ' player bluffs often.' : '.'))
        + (bm.why.length ? ' A well-chosen moment: ' + bm.why.join('; ') + '.' : ''));
      return why({ type: 'check' }, 'Checks with ' + made + ': ' + odds + ' — not enough to bet' + (n > 1 ? ' into ' + n + ' players' : '') + '.'
        + (adapt && bm.x < 0.5 && bm.why.length ? ' And it won’t bluff here: ' + bm.why[0] + '.' : ''));
    }
    const need = L.toCall / (L.pot + L.toCall);
    const price = 'to call it must win at least ' + pctW(need) + ' of the time (' + bbs(r2(L.toCall)) + ' to win a pot of ' + bbs(r2(L.pot + L.toCall)) + '), and ' + odds;
    if (trap) return why({ type: 'call' }, 'Just calls with ' + made + ' to trap — slow-playing a very strong hand (' + odds + ').');
    if (L.canRaise && e >= (n === 1 ? 0.72 : 0.62) && rng() < S.aggr * 0.7) return why(sized(g, i, g.curBet * 2.8), 'Raises with ' + made + ': ' + odds + ' — strong enough to build a bigger pot.');
    if (L.canRaise && drawy && rng() < S.bluff * 0.5 * Math.min(bm.x, 1.5)) return why(sized(g, i, g.curBet * 2.8), 'Raises as a semi-bluff: only ' + made + ' now, but it has a draw — it may win the pot at once, and can still improve if called.');
    if (e + S.sticky + (vsManiac ? 0.08 : 0) + (drawy ? 0.04 : 0) >= need + (S.foldToAggr || 0)) return why({ type: 'call' }, 'Calls with ' + made + ': ' + price + '.'
      + (e < need && vsManiac ? ' Not quite enough on paper, but a maniac bets with nothing so often that a good player calls it down lighter.' : e < need ? ' That’s not really enough — a ' + st + ' player calls too much.' : ''));
    return why({ type: 'fold' }, 'Folds ' + made + ': ' + price + ' — not enough.' + (S.foldToAggr ? ' A ' + st + ' player gives up easily when someone bets.' : ''));
  }
  function randomPlay(g, i, rng) {
    const L = legal(g, i), r = rng();
    if (L.toCall === 0) return r < 0.7 || !L.canRaise ? { type: 'check' } : sized(g, i, g.street ? L.pot * (0.3 + rng()) : openTo(g, i) + rng() * 3);
    if (r < 0.45) return { type: 'call' };
    if (r < 0.85 || !L.canRaise) return { type: 'fold' };
    return sized(g, i, g.curBet * (2 + rng() * 2));
  }
  // The sound play for seat i by the trainer's own grader, with its one-line conclusion — used to say
  // what a bot SHOULD have done when it plays at random. Its equity draw uses a fixed seed, so the
  // game's own random sequence is untouched.
  function soundPlay(g, i) {
    const s = spot(g, i), p = g.players[i], sp = !s.street && shortSpot(g, i);
    // the grader talks to the student ("you're ahead"); about a bot it should say "it"
    const so = why => (String(why || '').split('\n').find(l => /^So:/.test(l)) || '').replace(/^So:\s*/, '')
      .replace(/\bYou’re\b/g, 'It’s').replace(/\byou’re\b/g, 'it’s').replace(/\bYou\b/g, 'It').replace(/\byou\b/g, 'it').replace(/\bYour\b/g, 'Its').replace(/\byour\b/g, 'its').replace(/\byourself\b/g, 'itself');
    if (sp) { const go = gradeShort(g, i, sp.type === 'shove' ? 'raise' : 'call', p.bet + p.stack); return { kind: go.v === 'good' ? (sp.type === 'shove' ? 'raise' : 'call') : 'fold', so: so(go.why), s }; }
    if (!s.street) { const A = preflopAdvice(s.k, s); return { kind: A.best, so: so(A.why), s }; }
    const E = equityVsRanges(s.cards, s.board, s.opps, 2500, mulberry(7));
    const kinds = s.toCall > 0 ? ['raise', 'call', 'fold'] : ['raise', 'check'];
    const rated = kinds.map(k => ({ k, G: gradePost(s, k, E) }));
    const b = rated.find(r => r.G.v === 'good') || rated.find(r => r.G.v === 'ok') || rated[0];
    return { kind: b.k, so: so(b.G.why), s };
  }
  const botDecide = (g, i, rng) => {
    const lv = SKILL[g.players[i].level];
    if (lv && lv.err && rng() < lv.err) {
      const d = randomPlay(g, i, rng), name = g.players[i].name, L = legal(g, i);
      const did = d.type === 'call' && L.toCall === 0 ? 'check' : d.type === 'raise' && !L.canRaise ? 'call' : d.type;
      const who = name + ' is a ' + lv.name + ' player and plays more or less at random about ' + Math.round(lv.err * 100) + '% of the time — this was one of those. Real players at this level do the same.';
      let sound = null; try { sound = soundPlay(g, i); } catch (e) { sound = null; }
      if (!sound) return why(d, 'A random play: ' + who);
      const right = verbOf(sound.kind, sound.s), reason = sound.so ? ' ' + sound.so.replace(/^./, c => c.toUpperCase()) : '';
      if (sound.kind === did) return why(d, 'A fluke, but the right play: ' + who + ' This time the random choice was also the correct one — ' + right + '.' + reason);
      return why(d, 'A mistake — the right play was to ' + right + '.' + reason + ' ' + who);
    }
    return g.street === 0 ? botPreflop(g, i, rng) : botPostflop(g, i, rng);
  };

  // ---- grading the student ---------------------------------------------------------------------
  // Every explanation is a few short lines with a label each, in the same order: the facts (your
  // hand / your chance of winning / the price), "So:" — the conclusion in plain words — and
  // "Remember:", one rule to take away. The page bolds the labels (fmtWhy).
  const V = (v, head, why, loss) => ({ v, head, why, loss: Math.round((loss || 0) * 100) / 100 });
  const Adv = (best, alt, why, view) => ({ best, alt, why, view });
  const lines = (...a) => a.filter(Boolean).join('\n');
  // How good a starting hand is, in words: a verdict, its ranking, and how often you'd be dealt as good.
  function strengthWord(P) { return P <= 0.05 ? 'a premium hand' : P <= 0.15 ? 'a strong hand' : P <= 0.3 ? 'a good hand' : P <= 0.5 ? 'an average hand' : P <= 0.75 ? 'a weak hand' : 'a very weak hand'; }
  function oftenText(P) {
    if (P > 0.5) return 'About ' + Math.round(P * 10) + ' deals in 10 give you something better.';
    const n = Math.round(1 / P);
    return n <= 1 ? 'About half of all deals are as good or better.' : 'About 1 deal in ' + n + ' gives you a hand this good or better.';
  }
  function strength(k) {
    const P = pct()[k], rank = PK_HAND_ORDER.indexOf(k) + 1;
    return strengthWord(P) + ': ranked #' + rank + ' of the 169 different starting hands. ' + oftenText(P);
  }
  const share = key => r1(chartWidth(key) * 100) + '%';
  function preflopAdvice(k, x) {
    const has = key => chart(key).has(k);
    const you = 'Your hand: ' + k + ', ' + strength(k);
    if (x.raises === 0) {
      const lim = x.limpers || 0, limTxt = lim === 1 ? 'one player just called the big blind (limped)' : lim + ' players just called the big blind (limped)';
      if (x.pos === 'BB') return has('isoLimp')
        ? Adv('raise', ['check'], lines(you, 'The situation: nobody raised — ' + (lim ? limTxt : 'only the small blind called') + '. From the big blind, good players raise over limpers with about the best ' + share('isoLimp') + ' of hands.', 'So: ' + k + ' is strong enough — raise and make them pay to see the flop.', 'Remember: from the big blind, raise your good hands over limpers and check the rest — your flop is free.'), 'rfi.BTN')
        : Adv('check', ['raise'], lines(you, 'The situation: nobody raised, so the flop is free for you.', 'So: check and see the flop.', 'Remember: never fold when checking costs nothing.'), null);
      const key = 'rfi.' + x.pos;
      const sit = 'The situation: ' + (lim ? limTxt + ' in front of you and nobody has raised; you are in the ' + x.pos + '. From this seat, good players raise with about the best ' + share(key) + ' of hands — and raise a little bigger when there are limpers to charge.' : 'everyone folded to you in the ' + x.pos + '. From this seat, good players raise with about the best ' + share(key) + ' of hands.');
      return has(key)
        ? Adv('raise', [], lines(you, sit, 'So: ' + k + ' is good enough — raise.', 'Remember: the closer you sit to the button, the more hands you can raise, because fewer players are left behind you.'), key)
        : Adv('fold', [], lines(you, sit, 'So: ' + k + ' isn’t good enough from here — fold.', 'Remember: when you’re first in, raise or fold. Just calling (limping) lets everyone in cheaply.'), key);
    }
    if (x.raises === 1) {
      const grp = /^(CO|BTN|SB)$/.test(x.openerPos) ? 'Late' : 'Early';
      const who = x.pos === 'BB' ? 'bb' : x.pos === 'SB' ? 'sb' : 'ip';
      const k3 = who + '3' + grp, kc = who === 'sb' ? null : who + 'Call' + grp;
      const sit = 'The situation: the ' + x.openerPos + ' raised and it’s folded to you in the ' + x.pos + '. Here, good players re-raise (3-bet) the best ' + share(k3) + ' of hands'
        + (kc ? ', call with about another ' + share(kc) + ', and fold the rest.' : ' and fold everything else — from the small blind, calling leaves you stuck between the raiser and the big blind.');
      const rem = 'Remember: a raise from an early seat (UTG, UTG+1, LJ, HJ) usually means a strong hand, so continue with fewer hands against it than against a raise from the CO or button.';
      if (has(k3)) return Adv('raise', who === 'sb' ? [] : ['call'], lines(you, sit, 'So: ' + k + ' is strong enough to re-raise.', rem), who + grp);
      if (kc && has(kc) && x.depth != null && x.depth <= 40 && !/^(77|88|99|TT|JJ|AQs|AKs|KQs|AQo|AJs)$/.test(k)) return Adv('fold', ['call'], lines(you, sit, 'Your stack: ' + r1(x.depth) + ' big blinds. Between 20 and 40, a call with a hand like ' + k + ' can’t be followed up — there isn’t enough behind to make the flop worth seeing.', 'So: fold ' + k + ' here; with a stronger hand, re-raise all-in rather than call.', 'Remember: from 20 to 40 big blinds play tighter — fewer calls of raises, more re-raise-or-fold.'), who + grp);
      if (kc && has(kc)) return Adv('call', [], lines(you, sit, 'So: ' + k + ' is good enough to call, but not to re-raise.', rem), who + grp);
      return Adv('fold', [], lines(you, sit, 'So: ' + k + ' isn’t good enough to continue — fold.', rem), who + grp);
    }
    if (x.raises === 2) {
      if (x.heroOpened) {
        const sit = 'The situation: you raised and someone re-raised you (a 3-bet). Against that, re-raise again with the very best hands, call with good ones, and fold the rest.';
        const rem = 'Remember: a re-raise shows strength. Hands that looked good enough to raise often aren’t good enough to keep going.';
        if (has('vs3bet4')) return Adv('raise', ['call'], lines(you, sit, 'So: ' + k + ' is strong enough to raise again (a 4-bet).', rem), 'vs3');
        if (has('vs3betCall')) return Adv('call', [], lines(you, sit, 'So: ' + k + ' is too good to fold but not strong enough to raise again — call.', rem), 'vs3');
        return Adv('fold', [], lines(you, sit, 'So: ' + k + ' plays badly in a big pot against a strong hand — fold.', rem), 'vs3');
      }
      const sit = 'The situation: one player raised and another re-raised before it got to you. Two raises means two strong hands.';
      const rem = 'Remember: facing a raise and a re-raise, continue only with QQ, KK, AA and AK.';
      if (has('cold4')) return Adv('raise', ['call'], lines(you, sit, 'So: ' + k + ' is one of the very best hands — raise again.', rem), null);
      if (has('coldCall')) return Adv('call', ['raise'], lines(you, sit, 'So: ' + k + ' is strong enough to call.', rem), null);
      return Adv('fold', [], lines(you, sit, 'So: fold — ' + k + ' is behind the hands that raise and re-raise.', rem), null);
    }
    if (x.facingAllIn) {
      const sit = 'The situation: someone moved all-in for 100 big blinds — your whole stack is at risk.';
      const rem = 'Remember: deep-stacked, call an all-in only with QQ, KK, AA or AK.';
      return has('callJam') ? Adv('call', [], lines(you, sit, 'So: ' + k + ' is strong enough to call.', rem), 'vs4') : Adv('fold', [], lines(you, sit, 'So: fold — ' + k + ' isn’t strong enough to risk everything.', rem), 'vs4');
    }
    const sit = 'The situation: there has been a raise, a re-raise and another re-raise (a 4-bet). Only the very top hands continue.';
    const rem = 'Remember: against a 4-bet, go all-in with AA, KK or AK suited; call with QQ or AK offsuit; fold the rest.';
    if (has('jam4')) return Adv('raise', ['call'], lines(you, sit, 'So: ' + k + ' — go all-in.', rem), 'vs4');
    if (has('call4')) return Adv('call', ['raise'], lines(you, sit, 'So: ' + k + ' — call.', rem), 'vs4');
    return Adv('fold', [], lines(you, sit, 'So: fold — ' + k + ' isn’t strong enough.', rem), 'vs4');
  }
  function verbOf(kind, x) {
    if (kind !== 'raise') return kind;
    if (x.street) return x.toCall > 0 ? 'raise' : 'bet';
    return x.raises === 0 ? 'raise' : x.raises === 1 ? 're-raise (3-bet)' : x.raises === 2 ? 'raise again (4-bet)' : 'go all-in';
  }
  function gradePre(s, kind) {
    const A = preflopAdvice(s.k, s), best = verbOf(A.best, s);
    const G = kind === A.best ? V('good', 'Best play: ' + best, A.why, 0) : A.alt.indexOf(kind) >= 0 ? V('ok', 'Best play: ' + best + ' (yours was close)', A.why, 0) : V('bad', 'Best play: ' + best, A.why, 0);
    G.view = A.view; G.k = s.k; return G;
  }
  function gradePost(s, kind, E) {
    const n = s.opps.length, e = E / 100, d = draws(s.cards, s.board);
    const drawy = d.outs >= 8 && s.street < 3, weakDraw = d.outs >= 4 && d.outs < 8 && s.street < 3;   // a real draw (open-ended, flush) vs a gutshot
    const th = thresholds(s), vt = th.vt, rt = th.rt;
    const opp = n === 1 ? 'your opponent' : 'your ' + n + ' opponents';
    const chance = 'Your chance of winning: about ' + E + '%, against the hands ' + opp + ' are likely to have (judged from how they’ve played this hand).'
      + (th.notes.length ? '\nThe spot: ' + th.notes.join('; ') + '.' : '');
    const drawLine = (drawy || weakDraw) ? 'Your draw: ' + d.name + ' (' + d.outs + ' outs — cards that would make it). ' + (drawy ? 'If it hits on a later card you can win extra chips, so close calls are fine.' : 'A gutshot alone is a weak draw: it adds only a little.') : '';
    if (s.toCall > 0) {
      const need = s.toCall / (s.pot + s.toCall), ev = e * (s.pot + s.toCall) - s.toCall, np = r1(need * 100);
      const imp = d.outs >= 12 && s.street < 3 ? 0.08 : drawy ? 0.05 : weakDraw ? 0.02 : 0;   // implied odds: a draw that gets there wins more later; a gutshot only a little
      const price = 'The price: ' + bbs(s.toCall) + ' to call, to win a pot of ' + bbs(s.pot + s.toCall) + '. You need to win at least ' + np + '% of the time to break even (' + bbs(s.toCall) + ' ÷ ' + bbs(s.pot + s.toCall) + ').';
      const cmp = E + '% is ' + (e >= need ? 'more' : 'less') + ' than ' + np + '%';
      const money = ev >= 0 ? 'calling wins about ' + bbs(r2(ev)) + ' each time on average' : 'calling loses about ' + bbs(r2(-ev)) + ' each time on average';
      const rem = 'Remember: call when your chance of winning is bigger than the price; fold when it’s smaller.';
      const say = (v, head, so, remember, loss) => V(v, head, lines(chance, price, drawLine, 'So: ' + so, remember || rem), loss);
      if (kind === 'fold') {
        if (e + imp >= need + 0.05) return say('bad', 'Best play: call', cmp + ', so ' + money + '. Folding gave that up.', null, Math.max(0, ev));
        if (e + imp >= need) return say('ok', 'Best play: call — but it’s close', 'it’s close (' + cmp + '). Folding costs very little.');
        return say('good', 'Best play: fold', cmp + ', so ' + money + '. Folding saves those chips.');
      }
      if (kind === 'call') {
        if (e + imp < need - 0.05) return say('bad', 'Best play: fold', cmp + ', so ' + money + '. Fold hands like this.', null, Math.max(0, -ev));
        if (e >= rt) return say('ok', 'Best play: raise', 'you’re a big favourite. Calling is fine, but a raise makes worse hands pay more while you’re ahead.', 'Remember: when you’re well ahead, raise to build the pot.');
        if (e + imp < need) return say('ok', 'Best play: fold — but it’s close', drawy ? 'you’re a little short of the price, but your draw makes up for it.' : 'you’re a little short of the price, so calling costs a little over time.');
        return say('good', 'Best play: call', cmp + ', so ' + money + '.');
      }
      const remR = 'Remember: raise when you’re well ahead, or with a strong draw. Otherwise call or fold.';
      if (e >= rt) return say('good', 'Best play: raise', 'you’re a big favourite. Raising makes worse hands pay more.', remR);
      if (drawy) return say('ok', 'Best play: call or raise (a semi-bluff)', 'you’re behind for now, but your draw gives you a second way to win if they call. They may also fold straight away.', remR);
      if (e >= need) return say('ok', 'Best play: call', 'you have enough to call, but not enough to raise for value.', remR);
      return say('bad', 'Best play: ' + (e >= need ? 'call' : 'fold'), 'you’re behind most of their hands and have no draw to fall back on. A raise here mostly burns chips.', remR);
    }
    const sit = 'The situation: nobody has bet yet; the pot is ' + bbs(s.pot) + '. Against ' + opp + ' you want about ' + r1(vt * 100) + '% or more to bet for value.';
    const rem = 'Remember: bet when you’re ahead (or have a big draw). Check when you’re not sure.';
    const say = (v, head, so, remember) => V(v, head, lines(chance, sit, drawLine, 'So: ' + so, remember || rem), 0);
    if (kind === 'fold') return say('bad', 'Best play: check', 'checking was free. Folding gave up your share of the pot for nothing.', 'Remember: if nobody has bet, you can always check for free.');
    if (kind === 'check') {
      if (e >= vt + 0.15) return say('ok', 'Best play: bet', 'you’re well ahead. Checking lets them see the next card for free and you miss chips — bet next time.');
      return say('good', 'Best play: check', e >= vt ? 'you’re ahead, but not by much. Checking keeps the pot small — that’s fine.' : 'you’re not far enough ahead to bet for value. Checking is right.');
    }
    if (e >= vt) return say('good', 'Best play: bet', 'you’re ahead of most of their hands. Betting gets chips from worse hands.');
    if (drawy) return say('good', 'Best play: bet (a semi-bluff)', 'you’re behind now, but your draw gives you a second way to win. They may fold now, and if they call you can still hit.');
    if (e >= 0.35) return say('ok', 'Best play: check', 'you’re about even. A bet here mostly gets called by better hands and folds out worse ones.');
    const ops = stats.bluffOps || 0, rate = ops >= 5 ? (stats.bluffs || 0) / ops : 0;
    if (rate > 0.4) return V('bad', 'Best play: check', lines(chance, sit, drawLine, 'So: you’re behind, so this bet only works if they fold — and you’ve been bluffing ' + Math.round(rate * 100) + '% of these spots. That’s far too often: good players will stop folding.', 'Remember: a bluff only works because it is rare. Bluff about one spot in four at most.'), 0);
    return say('ok', 'Best play: check (a bluff now and then is fine)', 'you’re behind, so this bet only works if they fold. Fine now and then, best against one player.');
  }
  // Hero acts after every live opponent on this street? Postflop order is clockwise from the button.
  function inPosition(g, i) {
    const n = g.players.length, order = []; for (let k = 1; k <= n; k++) order.push((g.button + k) % n);
    const live = order.filter(j => !g.players[j].folded && !g.players[j].out);
    return live.length > 0 && live[live.length - 1] === i;
  }
  const sprOf = (g, i) => { const p = g.players[i], pot = potTotal(g) || 0; const eff = Math.min(p.stack, Math.max(0, Math.max.apply(null, g.players.filter((q, j) => j !== i && !q.folded).map(q => q.stack).concat([0])))); return pot > 0 ? Math.round(eff / pot * 10) / 10 : null; };
  // Postflop thresholds for betting (vt) and raising (rt): the base by player count, moved by position,
  // initiative and the stack-to-pot ratio. Each nudge is small and named, so the explanation can show it.
  function thresholds(s) {
    const n = s.opps.length;
    let vt = n === 1 ? 0.58 : n === 2 ? 0.44 : 0.36, rt = n === 1 ? 0.7 : 0.6;
    const notes = [];
    if (s.ip) { vt -= 0.03; notes.push('you act last (in position), so you can bet a little lighter'); }
    else if (s.ip === false && n === 1) { vt += 0.02; notes.push('you act first (out of position), so be a little more careful'); }
    if (s.initiative) { vt -= 0.04; notes.push('you raised before the flop, so a bet is expected of you (a continuation bet)'); }
    if (s.spr != null && s.spr <= 3) { vt -= 0.04; rt -= 0.05; notes.push('the stacks are small next to the pot (SPR ' + s.spr + '), so commit with less'); }
    else if (s.spr != null && s.spr >= 8) { vt += 0.03; rt += 0.03; notes.push('the stacks are deep next to the pot (SPR ' + s.spr + '), so build the pot only with real strength'); }
    return { vt: Math.max(0.28, Math.min(0.72, vt)), rt: Math.max(0.5, Math.min(0.85, rt)), notes };
  }
  // Short-stack tournament decisions are graded in prize money (ICM), with the chip answer beside it.
  // Returns null when the spot isn't push/fold, so the normal grading takes over.
  const usd = v => '$' + (Math.round(v * 100) / 100).toFixed(2);
  // Cash games have no prize pool: a short stack is graded on chips, straight from the equilibrium charts.
  function gradeShortCash(g, i, kind, to, sp) {
    const p = g.players[i], k = cls(p.cards[0], p.cards[1]), pos = posOf(g, i);
    const you = 'Your hand: ' + k + ', ' + strength(k);
    if (sp.type === 'shove') {
      const m = Math.max(1, sp.m), yes = PushFold.inPush(k, m, sp.S), pct = r1(PushFold.rangePct(PushFold.pushFreq(m, Math.max(1, Math.min(PushFold.MAX_S, Math.round(sp.S))))) * 100);
      const why = lines(you, 'Your stack: ' + r1(sp.S) + ' big blinds — short enough that the best plays are all-in or fold. ' + sp.m + ' player' + (sp.m > 1 ? 's are' : ' is') + ' still to act after you.',
        'The chart: from the ' + pos + ' at this stack, the equilibrium goes all-in with about ' + pct + '% of hands. ' + k + (yes ? ' is one of them.' : ' is not.'),
        'So: ' + (yes ? 'go all-in.' : 'fold.'), 'Remember: with 20 big blinds or fewer, don’t make small raises — go all-in or fold. The fewer players behind you, the more hands you can shove.');
      const act = kind === 'fold' ? 'fold' : (kind === 'raise' && to >= p.bet + p.stack - 0.01) ? 'shove' : kind === 'raise' ? 'small' : kind, best = yes ? 'shove' : 'fold';
      if (act === 'small' || act === 'call') return V(sp.S <= 12 ? 'bad' : 'ok', 'Best play: ' + (best === 'shove' ? 'all-in' : 'fold') + ' — not a small raise', why + '\nWhy not a small raise: it puts a big part of your stack in and still lets them see a flop or shove over you.', 0);
      return V(act === best ? 'good' : 'bad', 'Best play: ' + (best === 'shove' ? 'all-in' : 'fold'), why, 0);
    }
    const j = sp.mp, yes = PushFold.inCall(k, Math.max(1, j), 1, Math.max(1, Math.min(PushFold.MAX_S, Math.round(sp.S))));
    const why = lines(you, 'Facing an all-in of ' + r1(sp.S) + ' big blinds.', 'The chart: against a shove from there, the equilibrium calls with ' + k + (yes ? '.' : ' only at a shorter stack — here it folds.'), 'So: ' + (yes ? 'call.' : 'fold.'), 'Remember: calling an all-in needs a stronger hand than making one.');
    const act = kind === 'raise' ? 'call' : kind, best = yes ? 'call' : 'fold';
    return V(act === best ? 'good' : 'bad', 'Best play: ' + best, why, 0);
  }
  function gradeShort(g, i, kind, to) {
    const sp = shortSpot(g, i); if (!sp) return null;
    if (!g.tour) return gradeShortCash(g, i, kind, to, sp);
    const p = g.players[i], k = cls(p.cards[0], p.cards[1]), pos = posOf(g, i), pool = g.tour.payouts.reduce((a, b) => a + b, 0);
    const who = s => (g.players[s].name || 'Seat ' + s) + ' (' + posOf(g, s) + ', ' + r1(g.players[s].stack + g.players[s].bet) + 'bb)';
    const you = 'Your hand: ' + k + ', ' + strength(k);
    const close = d => Math.abs(d) < 0.0025 * pool;
    let res;
    if (sp.type === 'shove') {
      const tb = pfTable(g, i, sp.order), r = PushFold.shoveSpot(tb.t, k);
      const diff = r.shove$ - r.fold$, cdiff = r.shoveChips - r.foldChips, best = diff >= 0 ? 'shove' : 'fold';
      const inNash = PushFold.inPush(k, Math.max(1, sp.m), sp.S);
      const callers = r.callers.map(c => who(tb.seats[c.seat]) + ' would call with about ' + r1(c.callPct * 100) + '% of hands').join('; ');
      const why = lines(you,
        'Your stack: ' + r1(sp.S) + ' big blinds — short enough that the best plays are all-in or fold. ' + sp.m + ' player' + (sp.m > 1 ? 's are' : ' is') + ' still to act after you.',
        'The chart: from the ' + pos + ' at this stack, the correct strategy goes all-in with about ' + r1(r.heroRangePct * 100) + '% of hands. ' + k + (inNash ? ' is one of them.' : ' is not.'),
        'If you go all-in: everyone folds ' + r1(r.foldEquity * 100) + '% of the time and you win the blinds. ' + (callers ? callers + '.' : ''),
        'Prize money: going all-in is worth ' + usd(r.shove$) + ' to you; folding is worth ' + usd(r.fold$) + '.',
        (cdiff >= 0) !== (diff >= 0) ? 'Why prizes change it: counting chips alone, ' + (cdiff >= 0 ? 'all-in' : 'folding') + ' looks better. But near the prizes, losing your stack costs you more than doubling up gains — so ' + best + ' is right. This is called ICM.' : '',
        'So: ' + (best === 'shove' ? 'go all-in' : 'fold') + ' — it’s worth ' + usd(Math.abs(diff)) + ' more in prize money.',
        'Remember: with under about 12 big blinds, don’t make small raises — go all-in or fold. The fewer players behind you, the more hands you can shove.');
      const act = kind === 'fold' ? 'fold' : (kind === 'raise' && to >= p.bet + p.stack - 0.01) ? 'shove' : kind === 'raise' ? 'small' : kind;
      if (act === 'small' || act === 'call') res = V(sp.S <= 12 ? 'bad' : 'ok', 'Best play: ' + (best === 'shove' ? 'all-in' : 'fold') + ' — not a small raise', why + '\nWhy not a small raise: it puts a big part of your stack in, but still lets them see a flop cheaply. All-in makes them decide for everything.', 0);
      else if (act === best) res = V('good', 'Best play: ' + (best === 'shove' ? 'all-in' : 'fold'), why, 0);
      else res = V(close(diff) ? 'ok' : 'bad', 'Best play: ' + (best === 'shove' ? 'all-in' : 'fold') + (close(diff) ? ' — but it’s close' : ' (worth ' + usd(Math.abs(diff)) + ' more in prize money)'), why, 0);
      if (res.v === 'bad' && act !== 'small' && act !== 'call') res.usd = Math.abs(diff);
      return res;
    }
    const tb = pfTable(g, i, []), r = PushFold.callSpot(tb.t, k, tb.seats.indexOf(sp.pusher), Math.max(1, sp.mp));
    const best = r.call$ >= r.fold$ ? 'call' : 'fold', act = kind === 'fold' ? 'fold' : 'call', diff = r.call$ - r.fold$;
    const eq = r1(r.eq * 100), needI = r1(r.needIcm * 100), needC = r1(r.needChips * 100);
    const why = lines(you,
      'The situation: ' + who(sp.pusher) + ' went all-in for ' + r1(sp.S) + ' big blinds. From that seat, players go all-in with about ' + r1(r.pusherRangePct * 100) + '% of hands.',
      'Your chance of winning: about ' + eq + '% against those hands.',
      'The price: you need ' + needI + '% to call.' + (Math.abs(r.needIcm - r.needChips) >= 0.005 ? ' (If only chips mattered it would be ' + needC + '% — near the prizes, losing your stack hurts more, so you need more.)' : ''),
      'Prize money: calling is worth ' + usd(r.call$) + ' to you; folding is worth ' + usd(r.fold$) + '.',
      'So: ' + eq + '% is ' + (r.eq >= r.needIcm ? 'more' : 'less') + ' than ' + needI + '% — ' + best + '.',
      'Remember: against an all-in, compare your chance of winning with the price. Near the money, the price goes up.');
    if (act === best) res = V('good', 'Best play: ' + best, why, 0);
    else { res = V(close(diff) ? 'ok' : 'bad', 'Best play: ' + best + (close(diff) ? ' — but it’s close' : ' (worth ' + usd(Math.abs(diff)) + ' more in prize money)'), why, 0); if (res.v === 'bad') res.usd = Math.abs(diff); }
    return res;
  }
  // ---- bet sizing: the size a situation calls for, and why ----
  // Simple, standard guidance (what most good players do), stated as a range: preflop in big blinds
  // or multiples of the bet in front of you; after the flop as a share of the pot.
  function wetBoard(board) {
    if (board.length < 3) return false;
    const suits = [0, 0, 0, 0]; board.forEach(c => { suits[c.s]++; });
    const rs = Array.from(new Set(board.map(c => c.r))).sort((a, b) => a - b);
    let close = false; for (let k = 1; k < rs.length; k++) if (rs[k] - rs[k - 1] <= 2) close = true;
    return Math.max.apply(null, suits) >= 2 || close;
  }
  function sizeAdvice(s, E, drawy) {
    if (!s.street) {
      if (s.raises === 0) return s.pos === 'SB'
        ? { unit: 'bb', lo: 2.5, hi: 3.5, rec: '3 big blinds', why: 'From the small blind, open to about 3 big blinds — you’ll play the hand out of position, so make it a bit more expensive.' }
        : { unit: 'bb', lo: 2, hi: 3, rec: '2.5 big blinds', why: 'Open to 2–3 big blinds. That wins the blinds often enough; bigger risks more to win the same, and a limp lets everyone in cheaply.' };
      if (s.raises === 1) {
        const ip = !/^(SB|BB)$/.test(s.pos), m = ip ? 3 : 4;
        return { unit: 'x', lo: m - 0.6, hi: m + 0.8, rec: 'about ' + m + '× their raise', why: ip ? 'Re-raise to about 3× their raise when you’ll act after them for the rest of the hand.' : 'From the blinds, re-raise to about 4× their raise — you’ll act first after the flop, so charge them more to continue.' };
      }
      if (s.raises === 2) return { unit: 'x', lo: 2, hi: 2.7, rec: 'about 2.3× their re-raise', why: 'A 4-bet only needs to be about 2.3× — it already puts a big part of the stacks in.' };
      return null;
    }
    if (s.toCall > 0) return { unit: 'x', lo: 2.4, hi: 3.6, rec: 'about 3× their bet', why: 'Raise to about 3× their bet: smaller gives them a cheap price to call, bigger risks a lot to win the same.' };
    const e = E / 100, n = s.opps.length, vt = n === 1 ? 0.58 : n === 2 ? 0.44 : 0.36, wet = wetBoard(s.board);
    if (e >= 0.75) return wet
      ? { unit: 'pot', lo: 0.6, hi: 1.0, rec: 'about ¾ of the pot', why: 'Strong hand, and the board has possible draws: bet big (about ¾ of the pot) so drawing hands pay to chase.' }
      : { unit: 'pot', lo: 0.33, hi: 0.75, rec: '½ to ⅔ of the pot', why: 'Strong hand on a dry board (few draws): a medium bet (½–⅔ pot) gets called by weaker hands; a huge one scares them off.' };
    if (drawy) return { unit: 'pot', lo: 0.45, hi: 0.85, rec: 'about ⅔ of the pot', why: 'Semi-bluff with a draw: about ⅔ of the pot — big enough that they sometimes fold, and you can still hit if they call.' };
    if (e >= vt) return { unit: 'pot', lo: 0.25, hi: 0.6, rec: '⅓ to ½ of the pot', why: 'Medium-strength hand: a small bet (⅓–½ pot) gets called by worse hands without building a big pot you might lose.' };
    return { unit: 'pot', lo: 0.25, hi: 0.6, rec: '⅓ to ½ of the pot', why: 'Bluff: keep it small (⅓–½ pot). A bluff only has to work some of the time, and a small one risks less.' };
  }
  // The line added to a bet/raise grade: your size against the advice. off = 'small' | 'big' | null.
  function sizingLine(s, to, E, drawy) {
    const adv = sizeAdvice(s, E, drawy); if (!adv || !(to > 0)) return null;
    const allIn = to >= s.maxTo - 0.01;
    const val = adv.unit === 'bb' ? to : adv.unit === 'x' ? to / Math.max(s.curBet, 1e-9) : (to - s.myBet) / Math.max(s.pot, 1e-9);
    const shown = adv.unit === 'bb' ? r1(val) + ' big blinds' : adv.unit === 'x' ? r1(val) + '× ' + (s.street ? 'their bet' : 'the raise') : Math.round(val * 100) + '% of the pot';
    if (allIn && s.maxTo <= 25) return { off: null, line: 'Bet size: all-in — with a short stack that’s the natural size.' };
    const off = val < adv.lo - 1e-9 ? 'small' : val > adv.hi + 1e-9 ? 'big' : null;
    return { off, line: 'Bet size: you made it ' + (allIn ? 'all-in (' + shown + ')' : shown) + (off ? ' — too ' + off + '. Better: ' + adv.rec + '.' : ' — a good size.') + ' ' + adv.why };
  }
  function withSizing(G, s, kind, to, E) {
    if (kind !== 'raise') return G;
    const d = s.street ? draws(s.cards, s.board) : { outs: 0 };
    const z = sizingLine(s, to, E, d.outs >= 8 && s.street < 3); if (!z) return G;
    G.why += '\n' + z.line;
    if (z.off && G.v === 'good') G.v = 'ok';
    return G;
  }
  // ---- plain words: every short form spelled out ----
  // "2.5bb" → "2.5 big blinds"; "CO" → "Cutoff (CO)" the first time, "Cutoff" after; "AKs" → "Ace-King
  // suited (AKs)" the first time; ICM explained once. Safe to run twice: a code already in brackets is
  // left alone. Runs on explanations, hints, the coach's notes, drill questions and the feed — never
  // on the table's seat labels or the charts' grids, which keep their short forms and get a key.
  const POS_FULL = { UTG: 'Under the Gun', 'UTG+1': 'Under the Gun +1', LJ: 'Lojack', HJ: 'Hijack', CO: 'Cutoff', BTN: 'Button', SB: 'Small Blind', BB: 'Big Blind' };
  const RANK_WORD = { A: 'Ace', K: 'King', Q: 'Queen', J: 'Jack', T: 'Ten', 9: 'Nine', 8: 'Eight', 7: 'Seven', 6: 'Six', 5: 'Five', 4: 'Four', 3: 'Three', 2: 'Two' };
  const RANK_PLURAL = { A: 'Aces', K: 'Kings', Q: 'Queens', J: 'Jacks', T: 'Tens', 9: 'Nines', 8: 'Eights', 7: 'Sevens', 6: 'Sixes', 5: 'Fives', 4: 'Fours', 3: 'Threes', 2: 'Twos' };
  function handWords(k) {
    if (k[0] === k[1]) return 'a pair of ' + RANK_PLURAL[k[0]];
    return RANK_WORD[k[0]] + '-' + RANK_WORD[k[1]] + (k[2] === 's' ? ' suited' : k[2] === 'o' ? ' offsuit' : '');
  }
  function plain(text) {
    if (lvlIdx() >= 3) return String(text);                    // advanced / pro: the usual shorthand stays
    const seen = new Set();
    return String(text)
      .replace(/(\d+(?:\.\d+)?)\s?bb\b/g, (m, n) => n + (Number(n) === 1 ? ' big blind' : ' big blinds'))
      .replace(/(?<!\w)(UTG\+1|UTG|LJ|HJ|CO|BTN|SB|BB)(?!\w)/g, (m, p, at, str) => {
        if (str.slice(Math.max(0, at - POS_FULL[p].length - 2), at) === POS_FULL[p] + ' (') return m;   // already spelled out
        if (str[at - 1] === '(' && str[at + m.length] === ')') return POS_FULL[p];                          // "Rosa (SB)" → "Rosa (Small Blind)"
        if (seen.has(p)) return POS_FULL[p]; seen.add(p); return POS_FULL[p] + ' (' + p + ')';
      })
      .replace(/(?<![\w])([2-9TJQKA])([2-9TJQKA])([so])?(\+)?(?![\w])/g, (m, a, b, sfx, plus, at, str) => {
        if (a !== b && !sfx && !/[AKQJT]/.test(a)) return m;          // not a hand code (e.g. "52")
        if (!sfx && /^\d\d$/.test(a + b)) return m;                    // "33", "22": a number, not a pair, unless written 33s/33o
        if (/[.\d%]/.test(str[at + m.length] || '') || /[.\d]/.test(str[at - 1] || '')) return m;   // part of a number like 33.3%
        const k0 = a + b + (sfx || '');
        if (str[at - 1] === '(' && str.slice(0, at - 1).trimEnd().endsWith(handWords(k0))) return m;        // already spelled out
        if (str[at - 1] === '(') return m;                                                                  // "(A2o, …)" after the cards: the words follow elsewhere
        const k = a + b + (sfx || ''), words = handWords(k) + (plus ? (a === b ? ' or better' : ' or better kickers') : '');
        if (seen.has(m)) return words; seen.add(m); return words + ' (' + m + ')';
      })
      .replace(/(?<![(\w])ICM(?![\w)])/, 'ICM (the Independent Chip Model: what your chips are worth in prize money)');
  }
  // ---- detailed explanations: the numbers behind a decision, as tables ----
  // Optional ("📊 Show the numbers"). Worked out at the moment of the decision and kept with it, so a
  // replay shows the same tables. Plain data (title / head / rows), drawn by detailHtml.
  function tierName(hole, board) {
    const t = tierOn(hole, board);
    if (t === 3) return 'strong';
    if (t === 2) return 'top';
    if (t === 1) return (hole[0].r === hole[1].r || hole.some(h => board.some(b => b.r === h.r))) ? 'weak' : 'draw';
    return 'air';
  }
  const pctTxt = v => r1(v * 100) + '%';
  function topFreq(w) { const P = pct(), f = new Float64Array(169); PK_HAND_ORDER.forEach((c, j) => { f[j] = P[c] <= w + 1e-9 ? 1 : 0; }); return f; }
  function preDetail(s) {
    const h = PushFold.ix(s.k), rank = PK_HAND_ORDER.indexOf(s.k) + 1, eqVs = w => pctTxt(PushFold.eqVsRange(h, topFreq(w)));
    const out = [{ title: 'Your hand', head: ['', ''], rows: [['Hand', handWords(s.k) + ' (' + s.k + ')'], ['Rank among the 169 starting hands', '#' + rank + ' of 169'], ['Verdict', strengthWord(pct()[s.k])], ['How often you’re dealt this good or better', oftenText(pct()[s.k]).replace(/^About /, 'about ').replace(/.$/, '') + ' (' + pctTxt(pct()[s.k]) + ')']] }];
    const eqRows = [['Any two cards', eqVs(1)], ['The best 25% of hands', eqVs(0.25)], ['The best 10% of hands', eqVs(0.1)]];
    if (s.raises >= 1 && s.openerPos) { const o = s.opps.find(x => x.pos === s.openerPos); if (o && o.width < 1) eqRows.push(['The ' + s.openerPos + ' raiser’s likely hands (best ' + pctTxt(o.width) + ')', eqVs(o.width)]); }
    out.push({ title: 'Your chance of winning if all five cards are dealt, against…', head: ['Opponent holds', 'You win'], rows: eqRows });
    if (s.raises === 0 && s.pos !== 'BB') {
      out.push({ title: 'How much each seat raises when everyone folds to it', head: ['Seat', 'Raises with', 'Your hand?'],
        rows: ['UTG', 'UTG+1', 'LJ', 'HJ', 'CO', 'BTN', 'SB'].map(p => [p + (p === s.pos ? ' (you)' : ''), 'the best ' + pctTxt(chartWidth('rfi.' + p)), chart('rfi.' + p).has(s.k) ? 'raise' : 'fold']) });
    } else if (s.raises === 1) {
      const grp = /^(CO|BTN|SB)$/.test(s.openerPos) ? 'Late' : 'Early', who = s.pos === 'BB' ? 'bb' : s.pos === 'SB' ? 'sb' : 'ip';
      const w3 = chartWidth(who + '3' + grp), wc = who === 'sb' ? 0 : chartWidth(who + 'Call' + grp);
      out.push({ title: 'Against this raise, from your seat, good players…', head: ['Action', 'Share of hands', 'Your hand?'],
        rows: [['Re-raise (3-bet)', pctTxt(w3), chart(who + '3' + grp).has(s.k) ? 'yes' : ''], ['Call', who === 'sb' ? '0% — re-raise or fold' : pctTxt(wc), who !== 'sb' && chart(who + 'Call' + grp).has(s.k) ? 'yes' : ''], ['Fold', pctTxt(1 - w3 - wc), !chart(who + '3' + grp).has(s.k) && !(who !== 'sb' && chart(who + 'Call' + grp).has(s.k)) ? 'yes' : '']] });
    }
    return out;
  }
  function postDetail(s, E) {
    const out = [], e = E / 100, rng = Math.random;
    if (s.toCall > 0) {
      const need = s.toCall / (s.pot + s.toCall), ev = e * (s.pot + s.toCall) - s.toCall;
      out.push({ title: 'The price of calling', head: ['', ''], rows: [['Pot before you act', bbs(r2(s.pot))], ['To call', bbs(r2(s.toCall))], ['Pot if you call', bbs(r2(s.pot + s.toCall))],
        ['Chance you need (to call ÷ pot if you call)', pctTxt(need)], ['Your chance of winning', E + '%'], ['Calling, on average', (ev >= 0 ? '+' : '') + bbs(r2(ev)) + ' each time'], ['Folding', 'nothing more lost']] });
    }
    // what each opponent probably holds, judged from how they've played
    const base = new Uint8Array(52); s.cards.concat(s.board).forEach(c => { base[cid(c)] = 1; });
    const mine = evalHand(s.cards.concat(s.board)), N = 600, rows = [];
    for (const o of s.opps) {
      const mix = { strong: 0, top: 0, weak: 0, draw: 0, air: 0 }; let ahead = 0;
      for (let t = 0; t < N; t++) {
        const c = sampleHand(o, s.board, base.slice(), rng); if (!c) continue;
        mix[tierName([c.x, c.y], s.board)]++;
        const theirs = evalHand([c.x, c.y].concat(s.board)); if (mine > theirs) ahead++; else if (mine === theirs) ahead += 0.5;
      }
      const eqv = equityVsRanges(s.cards, s.board, [o], 1200);
      rows.push([(o.name || 'Player') + ' (' + o.pos + ')', pctTxt(mix.strong / N), pctTxt(mix.top / N), pctTxt(mix.weak / N), pctTxt(mix.draw / N), pctTxt(mix.air / N), pctTxt(ahead / N), eqv + '%']);
    }
    out.push({ title: 'What they probably hold (from how they’ve played this hand)', head: ['Player', 'Two pair or better', 'Top pair / overpair', 'Weaker pair', 'A draw', 'Nothing', 'You’re ahead right now', 'Your chance vs them'], rows,
      note: 'Their likely hands are estimated from their seat and their bets, checks and calls — the same reads the grades use.' });
    // outs: cards still to come that improve your hand (not cards that only improve the board)
    if (s.street < 3) {
      const CATS = ['high card', 'one pair', 'two pair', 'three of a kind', 'a straight', 'a flush', 'a full house', 'four of a kind', 'a straight flush'];
      const cat = cs => Math.floor(evalHand(cs) / CAT), cur = cat(s.cards.concat(s.board)), by = {};
      let total = 0, unseen = 0;
      for (let id = 0; id < 52; id++) {
        if (base[id]) continue; unseen++;
        const c = fromId(id), nc = cat(s.cards.concat(s.board, [c])), bc = cat(s.board.concat([c]));
        if (nc > cur && nc > bc && nc >= 2) { by[CATS[nc]] = (by[CATS[nc]] || 0) + 1; total++; }
      }
      const orows = Object.keys(by).sort((a, b) => CATS.indexOf(b) - CATS.indexOf(a)).map(k => ['Makes ' + k, by[k] + ' card' + (by[k] === 1 ? '' : 's')]);
      orows.push(['All your outs', total + ' of the ' + unseen + ' unseen cards']);
      orows.push(['Chance on the next card', pctTxt(total / unseen)]);
      if (s.street === 1) orows.push(['Chance by the river (two cards)', pctTxt(1 - (unseen - total) * (unseen - total - 1) / (unseen * (unseen - 1)))]);
      out.push({ title: 'Your outs — cards to come that improve you', head: ['', ''], rows: orows,
        note: 'An out improves your hand; it doesn’t guarantee the win. Rule of thumb: outs × 2 = % for one card, outs × 4 = % for two.' });
    }
    return out;
  }
  function shortDetail(G, i, sp) {
    if (!G.tour) return [];                                                       // cash: no prize-money tables
    const p = G.players[i], k = cls(p.cards[0], p.cards[1]), name = s2 => (G.players[s2].name || 'Seat') + ' (' + posOf(G, s2) + ', ' + r1(G.players[s2].stack + G.players[s2].bet) + 'bb)';
    if (sp.type === 'shove') {
      const tb = pfTable(G, i, sp.order), r = PushFold.shoveSpot(tb.t, k), out = [];
      out.push({ title: 'If you go all-in, each player behind you…', head: ['Player', 'Calls with', 'Needs to call (prize money)', 'Needs to call (chips only)'],
        rows: r.callers.map(c => [name(tb.seats[c.seat]), pctTxt(c.callPct) + ' of hands', pctTxt(c.needIcm), pctTxt(c.needChips)]) });
      const rows = [['You fold', usd(r.fold$)], ['All-in, everyone folds (' + pctTxt(r.foldEquity) + ' of the time)', usd(r.steal$)]];
      r.callers.forEach(c => { const nm = G.players[tb.seats[c.seat]].name; rows.push(['All-in, ' + nm + ' calls, you win', usd(c.win$)], ['All-in, ' + nm + ' calls, you lose', usd(c.lose$)]); });
      rows.push(['Going all-in, on average', usd(r.shove$)]);
      out.push({ title: 'What each outcome is worth to you in prize money', head: ['Outcome', 'Prize money'], rows, note: 'Prize money = your share of the prizes from your chips (ICM).' });
      return out;
    }
    const tb = pfTable(G, i, []), r = PushFold.callSpot(tb.t, k, tb.seats.indexOf(sp.pusher), Math.max(1, sp.mp));
    return [{ title: 'Calling the all-in', head: ['', ''], rows: [['Their likely hands', 'the best ' + pctTxt(r.pusherRangePct)], ['Your chance of winning', pctTxt(r.eq)], ['Chance you need (chips only)', pctTxt(r.needChips)], ['Chance you need (prize money)', pctTxt(r.needIcm)]] },
      { title: 'What each outcome is worth to you in prize money', head: ['Outcome', 'Prize money'], rows: [['You fold', usd(r.fold$)], ['You call and win', usd(r.win$)], ['You call and lose', usd(r.lose$)], ['Calling, on average', usd(r.call$)]], note: 'Prize money = your share of the prizes from your chips (ICM).' }];
  }
  function detailFor(G, i, E) {
    try {
      const s = spot(G, i), sp = !s.street && G.tour && shortSpot(G, i);
      if (sp) return shortDetail(G, i, sp);
      if (!s.street) return preDetail(s);
      return postDetail(s, E == null ? equityVsRanges(s.cards, s.board, s.opps, 2500) : E);
    } catch (e) { console.error('detail', e); return null; }
  }
  function detailHtml(tables, toggle) {
    const btn = toggle ? '<button class="ghost tr-mini" data-act="ui:detail">' + (opts.detail ? 'Hide the numbers' : '📊 Show the numbers') + '</button>' : '';
    if (!opts.detail || !tables || !tables.length) return btn ? '<div class="tr-row">' + btn + '</div>' : '';
    return '<div class="tr-detail">' + tables.map(t => '<div class="tr-stattab"><b>' + esc(plain(t.title)) + '</b><div class="tr-tscroll"><table>'
      + (t.head && t.head.some(Boolean) ? '<tr>' + t.head.map(x => '<th>' + esc(plain(x)) + '</th>').join('') + '</tr>' : '')
      + t.rows.map(r => '<tr>' + r.map(x => '<td>' + esc(plain(String(x))) + '</td>').join('') + '</tr>').join('') + '</table></div>'
      + (t.note ? '<small>' + esc(plain(t.note)) + '</small>' : '') + '</div>').join('') + (btn ? '<div class="tr-row">' + btn + '</div>' : '') + '</div>';
  }

  // Explanation text → HTML: escaped, with each line's label ("So:", "The price:") in bold.
  function fmtWhy(text) {
    return esc(plain(levelWhy(text))).split('\n').map(l => l.replace(/^([A-Z][A-Za-z’' ]{1,28}):/, '<b class="tr-lbl">$1:</b>')).join('\n');
  }

  // The decision in front of seat i, as that player can see it (their cards; everyone else's ranges).
  function spot(g, i) {
    i = i || 0;
    const p = g.players[i], L = legal(g, i);
    return {
      street: g.street, pos: posOf(g, i), k: cls(p.cards[0], p.cards[1]), cards: p.cards.slice(), board: g.board.slice(),
      pot: L.pot, toCall: L.toCall, raises: g.raises, curBet: g.curBet, myBet: p.bet, maxTo: L.maxTo, openerPos: g.openerSeat >= 0 ? posOf(g, g.openerSeat) : '', heroOpened: g.openerSeat === i,
      facingAllIn: g.street === 0 && g.players.some((q, j) => j !== i && !q.folded && q.allin && q.bet >= g.curBet),
      limpers: g.street === 0 && g.raises === 0 ? g.log.filter(l => l.st === 0 && l.kind === 'call').length : 0,   // players who just called the big blind before you
      opps: g.players.map((q, j) => ({ q, j })).filter(o => o.j !== i && !o.q.folded).map(o => ({ width: o.q.rangeW, set: o.q.rangeSet, post: o.q.post.slice(), name: o.q.name, pos: posOf(g, o.j) })),
      ip: inPosition(g, i), initiative: g.lastRaiser === i, spr: sprOf(g, i), depth: effStack(g, i),
    };
  }
  // A person at the table (you, or a friend) has no bot style.
  const isHuman = p => !!p && !p.style;
  function historyText(g, decisions) {
    const out = ["Trainer hand #" + g.handNo + " — " + g.players.length + "-handed No-Limit Hold'em, blinds 0.5/1bb, everyone 100bb (practice table; seats without a person are bots)."];
    g.players.forEach((p, i) => out.push(posOf(g, i) + ': ' + p.name + (isHuman(p) ? ' (player)' : ' — bot, ' + botLabel(p)) + (p.cards ? ' ' + cardsTxt(p.cards) : '')));
    for (let st = 0; st <= 3; st++) {
      const acts = g.log.filter(l => l.st === st); if (!acts.length && st > g.street) break;
      const b = st === 1 ? g.board.slice(0, 3) : st === 2 ? g.board.slice(0, 4) : st === 3 ? g.board : [];
      out.push(STREET[st].toUpperCase() + (b.length ? ' [' + cardsTxt(b) + ']' : '') + ':');
      acts.forEach(l => out.push('  ' + l.pos + ' ' + g.players[l.i].name + ' ' + l.txt));
    }
    if (g.result) g.result.wins.forEach(w => out.push('Result: ' + g.players[w.i].name + ' wins ' + bbs(Math.round(w.amt * 100) / 100) + (w.name ? ' with ' + w.name : '')));
    if (decisions && decisions.length) {
      out.push("TRAINER'S GRADES (computed in code; equity is against each opponent's likely range, and where shown also against the cards they actually held):");
      decisions.forEach(d => out.push('  ' + STREET[d.street] + ': ' + (d.name || 'hero') + ' ' + d.kind + ' — ' + d.G.v.toUpperCase() + ': ' + d.G.head + '. ' + d.G.why
        + (d.Eact != null ? ' Against the actual cards: ' + d.Eact + '%.' : '')));
    }
    return out.join('\n');
  }

  // =================================================================================================
  // UI
  // =================================================================================================
  const TABS = [['play', '🃏 Play'], ['learn', '📘 Learn'], ['hands', '📜 Hand history'], ['pf', 'Push/fold'], ['icm', 'Prize money (ICM)'], ['pre', 'Preflop'], ['odds', 'Pot odds'], ['eq', 'Equity'], ['outs', 'Outs'], ['sd', 'Showdown'], ['charts', 'Charts'], ['stats', 'Stats']];
  const LAYOUT = {
    6: { seat: [[50, 101], [5, 76], [8, 16], [50, -4], [92, 16], [95, 76]], bet: [[50, 74], [22, 64], [24, 32], [50, 20], [76, 32], [78, 64]], deal: [[60, 80], [17, 52], [18, 40], [61, 15], [82, 40], [83, 52]] },
    8: { seat: [[50, 101], [19, 94], [-5, 47], [19, 2], [50, -5], [81, 2], [105, 47], [81, 94]],
         bet: [[50, 72], [37, 66], [16, 47], [33, 33], [61, 24], [67, 33], [84, 47], [63, 66]],
         deal: [[64, 80], [35, 86], [9, 64], [34, 14], [61, 14], [66, 14], [91, 64], [65, 86]] },
  };
  const layout = () => LAYOUT[g.players.length] || LAYOUT[8];
  const BOT_MS = 650, BOT_MS_FAST = 260;
  const AI_COACH = "You are an expert No-Limit Hold'em coach reviewing ONE practice hand from a training app (bots, and sometimes friends at the same table — coach every player whose decisions are graded). "
    + 'The app has already computed the maths — equities against estimated ranges and pot odds are in the text. Use those numbers; never invent different ones. '
    + 'Explain in plain English: the key decision points, what a strong player does there and why (ranges, position, board texture, bet sizing, blockers), '
    + 'and finish with ONE concrete lesson to remember. Be direct, under 300 words, no preamble.';
  const DEF_STATS = () => ({ hands: 0, net: 0, vpip: 0, pfr: 0, good: 0, ok: 0, bad: 0, loss: 0, hints: 0, leaks: {}, drills: { pre: [0, 0], odds: [0, 0], eq: [0, 0, 0], outs: [0, 0], sd: [0, 0], pf: [0, 0], icm: [0, 0, 0] } });
  let lsWarned = false;
  const ls = (k, v) => { try { if (v === undefined) return localStorage.getItem(k); localStorage.setItem(k, v); } catch (e) { if (v !== undefined && !lsWarned) { lsWarned = true; try { toast('Couldn’t save (the browser’s storage is full or blocked) — your progress this session may not be kept', 'red'); } catch (x) {} } } return null; };
  const load = (k, def) => { try { const v = JSON.parse(ls(k) || 'null'); return v ? Object.assign(def, v) : def; } catch (e) { return def; } };
  let stats = load(STATS_KEY, DEF_STATS()), opts = load(OPT_KEY, { showBots: false, pause: true, advise: true });
  stats.drills = Object.assign(DEF_STATS().drills, stats.drills);   // stats saved before a drill existed still load
  // ---- 🎓 coaching level: who is being coached ------------------------------------------------------
  // The same maths for everyone; what changes is how it's said. Beginners get every term explained
  // (a "Words used" list under each explanation), the usual shorthand spelled out, and the advice shown
  // before they act; advanced players get the shorthand and no reminders; a pro gets the answer first
  // and the numbers, nothing else.
  const COACH_LEVELS = [
    ['new', 'Absolute beginner', 'Nothing assumed: every poker word is explained under each explanation, every time.'],
    ['beginner', 'Beginner', 'Plain words throughout; each poker term is explained the first time it comes up.'],
    ['improver', 'Improver', 'The standard explanations: the facts, the conclusion and a rule to remember.'],
    ['advanced', 'Advanced', 'Shorter, in the usual poker shorthand (UTG, 3-bet, 94o), without the reminders.'],
    ['pro', 'Pro', 'The answer first, then the numbers. No basics, no reminders.'],
  ];
  const lvl = () => COACH_LEVELS.some(l => l[0] === opts.level) ? opts.level : 'beginner';
  const lvlIdx = () => COACH_LEVELS.findIndex(l => l[0] === lvl());
  const lvlName = () => COACH_LEVELS[lvlIdx()][1];
  // Poker words, in beginner's terms. Checked against each explanation; the ones it uses are listed under it.
  const GLOSSARY = [
    [/\b(3-bet|re-rais)/i, '3-bet (re-raise)', 'raising again after someone has already raised.'],
    [/\b4-bet/i, '4-bet', 'the third raise in a row — a raise of a re-raise.'],
    [/pot odds|\bthe price\b|break even/i, 'the price (pot odds)', 'what you must pay to call, compared with what you can win. Pay 3 to win 12 and you need to win 1 time in 4 — 25%.'],
    [/chance of winning|equity/i, 'chance of winning (equity)', 'how often your hand would win if the rest of the cards were dealt out — the trainer deals the rest of the hand thousands of times to find it.'],
    [/\bposition\b|in position|out of position|acts? (first|last|after)/i, 'position', 'where you sit compared with the dealer button. Acting after the others is better — you see what they do first.'],
    [/\bbutton\b|\bBTN\b/i, 'the button', 'the dealer seat. It moves one seat left every hand; the player on it acts last after the flop.'],
    [/\bblinds?\b|\bbig blinds?\b/i, 'the blinds', 'the two forced bets paid before the cards are dealt (small blind and big blind). Every amount here is measured in big blinds.'],
    [/\blimp/i, 'limping', 'just calling the big blind before the flop instead of raising.'],
    [/all-in/i, 'all-in', 'betting every chip you have.'],
    [/flush draw|straight draw|\bdraws?\b|drawing hand/i, 'a draw', 'a hand that isn’t made yet but will be if the right card comes — four cards to a flush or a straight.'],
    [/\bouts?\b/i, 'outs', 'the cards still to come that would make your hand.'],
    [/implied odds/i, 'implied odds', 'the extra chips you can win later if your draw hits — what makes a close call worth it.'],
    [/for value|value bet/i, 'betting for value', 'betting because you think you have the best hand and want worse hands to call.'],
    [/semi-bluff/i, 'a semi-bluff', 'a bet with a hand that’s probably behind now but has a draw to become the best.'],
    [/\bbluff/i, 'a bluff', 'betting with a weak hand to make better hands fold.'],
    [/\branges?\b|likely to have|likely holds/i, 'a range', 'all the hands a player could have here, judging by how they’ve played so far.'],
    [/overpair/i, 'an overpair', 'a pocket pair higher than every card on the board.'],
    [/top pair/i, 'top pair', 'pairing the highest card on the board.'],
    [/kicker/i, 'the kicker', 'your other card — it decides ties between the same pairs.'],
    [/c-bet|continuation bet/i, 'a c-bet (continuation bet)', 'the player who raised before the flop betting again on the flop.'],
    [/effective stack|\bSPR\b/i, 'the effective stack', 'the smaller of the two stacks in a pot — the most that can actually be won or lost.'],
    [/\bICM\b|prize money/i, 'ICM (prize money)', 'what your chips are worth in prize money in a tournament, where staying in matters more than chips.'],
    [/\bante/i, 'the ante', 'a small forced bet everyone pays each hand in a tournament.'],
    [/showdown/i, 'the showdown', 'when the betting is finished and the players left turn their cards over — best hand wins.'],
    [/suited|offsuit/i, 'suited / offsuit', 'suited = both your cards the same suit (a flush is possible); offsuit = different suits.'],
    [/\b(flop|turn|river)\b/i, 'the flop, turn and river', 'the shared cards: the flop is the first three, the turn the fourth, the river the fifth and last.'],
    [/\bcheck(s|ing|ed)?\b/i, 'check', 'pass without betting when nobody has bet yet; the next player acts.'],
    [/\bfold(s|ing|ed)?\b/i, 'fold', 'give up the hand; any chips you’ve already put in stay in the pot.'],
    [/\bcall(s|ing|ed)?\b/i, 'call', 'match the bet in front of you and stay in the hand.'],
    [/\brais(e|es|ing|ed)\b/i, 'raise', 'put in more than the bet in front of you, so the others must pay more to stay in.'],
    [/premium hand|strong hand|starting hand/i, 'starting hands', 'your two private cards; of the 169 kinds, pairs and two high cards of one suit are the best.'],
  ];
  let explained = new Set();        // beginner: each word is explained once a session
  // An explanation, as this level should read it. Pure: the level can be passed in (tests).
  function levelWhy(text, level) {
    const L = level || lvl(), i = COACH_LEVELS.findIndex(l => l[0] === L);
    let lines = String(text || '').split('\n').filter(Boolean);
    if (i >= 3) lines = lines.filter(l => !/^Remember:/.test(l));
    if (i >= 4) { lines = lines.filter(l => !/^Note:/.test(l)); const so = lines.findIndex(l => /^So:/.test(l)); if (so > 0) lines.unshift(lines.splice(so, 1)[0]); }
    if (i <= 1) {
      const body = lines.join('\n'), hits = GLOSSARY.map(gl => ({ gl, at: body.search(gl[0]) })).filter(h => h.at >= 0).sort((a, b) => a.at - b.at);
      const fresh = i === 0 ? hits.slice(0, 4) : hits.filter(h => !explained.has(h.gl[1])).slice(0, 3);
      if (fresh.length) { lines.push('Words used:'); fresh.forEach(h => { explained.add(h.gl[1]); lines.push('• ' + h.gl[1] + ' — ' + h.gl[2]); }); }
    }
    return lines.join('\n');
  }
  function levelSelHtml() {
    return '<label class="tr-level" title="Changes how every explanation is written, not the advice itself">🎓 Coaching level: <select data-sel="level">' + COACH_LEVELS.map(l => '<option value="' + l[0] + '"' + (l[0] === lvl() ? ' selected' : '') + '>' + esc(l[1]) + '</option>').join('') + '</select></label>';
  }
  function setLevel(v) {
    if (!COACH_LEVELS.some(l => l[0] === v)) return;
    opts.level = v;
    const i = lvlIdx();
    if (i <= 1) { opts.advise = true; opts.detail = false; }       // sensible defaults for the level; the tick boxes still change them
    if (i === 0) { opts.showBots = true; opts.pause = true; opts.stepBots = true; }   // a teaching table: every card face up, one move at a time
    if (i === 3) opts.detail = true;
    if (i === 4) { opts.advise = false; opts.detail = true; }
    saveOpts(); explained = new Set(); said = new Set(); spokenLast = '';
    toast('Coaching level: ' + lvlName() + ' — ' + COACH_LEVELS[i][2], 'green');
    renderMain();
  }
  // What the AI coach is told about the student.
  // ---- absolute beginner: the hand itself, explained as it happens ----
  // Someone who has never played needs the deal, the blinds, the button, the order of play, what each
  // shared card is and how the winner is decided — before any strategy. At the "Absolute beginner"
  // level this block leads the right-hand column at every stage of every hand (and is read aloud).
  const HAND_RANKS = [
    ['Royal flush', 'Ten, Jack, Queen, King, Ace, all of one suit — the best hand there is.'],
    ['Straight flush', 'five cards in a row, all of one suit.'],
    ['Four of a kind', 'four cards of the same rank, like four Nines.'],
    ['Full house', 'three of one rank and two of another, like three Kings and two Fours.'],
    ['Flush', 'five cards of one suit, in any order.'],
    ['Straight', 'five cards in a row, suits mixed, like 7-8-9-10-Jack.'],
    ['Three of a kind', 'three cards of the same rank.'],
    ['Two pair', 'two cards of one rank and two of another.'],
    ['One pair', 'two cards of the same rank.'],
    ['High card', 'none of the above — the highest card decides.'],
  ];
  const rankOf = name => { const n = String(name || ''); return /royal/i.test(n) ? 0 : /straight flush/i.test(n) ? 1 : /^four/i.test(n) ? 2 : /full house/i.test(n) ? 3 : /^flush/i.test(n) ? 4 : /^straight/i.test(n) ? 5 : /^three/i.test(n) ? 6 : /two pair/i.test(n) ? 7 : /pair/i.test(n) ? 8 : 9; };
  const ranksHtml = () => '<details class="tr-ranks"><summary>The 10 kinds of hand, best first</summary><div class="tr-why">' + HAND_RANKS.map((r, k) => (k + 1) + '. <b>' + r[0] + '</b> — ' + r[1]).join('\n') + '\nA hand is always your best FIVE cards out of your two and the five shared ones.</div></details>';
  function primerHtml(G, M) {
    const g = G || Trainer_g(), me = M == null ? Trainer_me() : M;
    if (lvl() !== 'new' || !g || me < 0) return '';
    const p = g.players[me], n = g.players.length, you = autoOn() ? 'the Angel' : 'you', your = autoOn() ? 'the Angel’s' : 'your';
    const bb = g.tour ? 'big blind' : '1 big blind', sb = g.tour ? 'half of it' : 'half a big blind';
    let head, body;
    if (g.over && g.result) {
      const w = g.result.wins[0], who = w.i === me ? (autoOn() ? 'The Angel' : 'You') : g.players[w.i].name;
      if (g.result.showdown) {
        const r = rankOf(w.name);
        head = 'The showdown';
        body = 'The betting is finished and more than one player is still in, so they turn their cards over. ' + who + (w.i === me && !autoOn() ? ' win' : ' wins') + ' with ' + (w.name || 'the best hand') + ' — that’s ' + (r === 9 ? 'a high card, the lowest kind of hand' : 'a ' + HAND_RANKS[r][0].toLowerCase() + ', number ' + (r + 1) + ' of the 10 kinds of hand') + '. The pot — every chip bet during the hand — goes to the winner.';
      } else {
        head = 'Everyone else folded';
        body = who + (w.i === me && !autoOn() ? ' win' : ' wins') + ' the pot without showing any cards. That’s allowed — a hand can be won without the best cards, which is why betting matters as much as the cards.';
      }
      return '<div class="tr-explain tr-primer"><b>🧭 ' + esc(head) + '</b><div class="tr-why">' + esc(body) + '</div>' + ranksHtml() + '</div>';
    }
    if (!p || !p.cards || !p.cards.length) return '';
    const mine = !g.over && g.toAct === me;
    if (g.street === 0) {
      head = 'A new hand';
      const faceUp = autoOn() || opts.showBots || (room && room.faceUp);
      body = 'Everyone has been dealt two cards face down. ' + (faceUp ? 'In a real game only you would see ' + your + ' two — here every card is face up, to help you learn. ' : 'Only you can see ' + your + ' two — the others’ are hidden until the end. ') + (g.handNo === 1 ? 'There are ' + n + ' players at this table. ' : '')
        + 'Before the deal, the two players to the left of the dealer button (the D) had to pay the blinds — forced bets of ' + sb + ' and ' + bb + ' — so there’s something to win. '
        + 'Betting goes clockwise, starting with the player after the big blind. In turn, each player either folds (throws the cards away and is out of the hand), calls (matches the biggest bet so far) or raises (bets more, so the others must pay more to stay). '
        + 'The aim right now: decide whether ' + your + ' two cards are worth paying to play.';
    } else if (g.street === 1) {
      head = 'The flop';
      body = 'Three shared cards are turned over in the middle. Everyone still in uses any of them with their own two cards to make the best five-card hand. Another round of betting now, starting with the first player still in after the dealer button. If nobody has bet yet, ' + you + ' can check — stay in without paying.';
    } else if (g.street === 2) {
      head = 'The turn';
      body = 'A fourth shared card. One more round of betting. Hands that were nearly made — four to a flush, four to a straight — have one card left to come.';
    } else {
      head = 'The river';
      body = 'The fifth and last shared card — no more cards to come, so what ' + you + ' hold now is what ' + you + ' finish with. After this round of betting, anyone still in shows their cards and the best five-card hand wins the pot.';
    }
    if (mine && !autoOn()) body += ' It’s your turn: the buttons under the table are your choices, and the one marked Recommended is the coach’s advice.';
    return '<div class="tr-explain tr-primer"><b>🧭 ' + esc(head) + '</b><div class="tr-why">' + esc(body) + '</div>' + (g.handNo === 1 && g.street === 0 ? ranksHtml() + '<div class="tr-dim">For the whole picture, see 📘 Learn → How a hand works.</div>' : '') + '</div>';
  }
  const levelAiLine = () => 'THE STUDENT IS ' + ({ new: 'AN ABSOLUTE BEGINNER: explain every poker term you use in plain words, assume nothing, keep the numbers simple (e.g. "1 time in 4")',
    beginner: 'A BEGINNER: plain words, explain each poker term the first time you use it', improver: 'AN IMPROVING PLAYER: normal coaching language',
    advanced: 'AN ADVANCED PLAYER: be concise and use standard poker shorthand', pro: 'A PROFESSIONAL: the key numbers and the line, no basics' })[lvl()] + '.';
  const saveStats = () => { stats.lastSeen = Date.now(); ls(STATS_KEY, JSON.stringify(stats)); }, saveOpts = () => ls(OPT_KEY, JSON.stringify(opts));
  // A sitting ends when two hours pass without play (or on the Stats tab's button). The totals at that
  // moment are kept, so each sitting is the difference between two snapshots — what moved this week.
  const SIT_GAP = 2 * 3600000;
  const snapOf = () => ({ when: Date.now(), hands: stats.hands, net: stats.net, good: stats.good, ok: stats.ok, bad: stats.bad, loss: stats.loss, street: JSON.parse(JSON.stringify(stats.byStreet || [])), drills: JSON.parse(JSON.stringify(stats.drills)) });
  function closeSitting(force) {
    const last = (stats.sessions || [])[(stats.sessions || []).length - 1];
    const moved = !last || last.hands !== stats.hands || (last.good + last.ok + last.bad) !== (stats.good + stats.ok + stats.bad) || JSON.stringify(last.drills) !== JSON.stringify(stats.drills);
    if (!moved) return false;
    if (!force && !(stats.lastSeen && Date.now() - stats.lastSeen > SIT_GAP)) return false;
    const snap = snapOf(); if (!force) snap.when = stats.lastSeen;
    stats.sessions = (stats.sessions || []).concat([snap]).slice(-40); saveStats(); return true;
  }
  let shown = false, tab = 'play', g = null, token = 0, decisions = [], chartView = 'rfi.UTG';
  const drill = {};
  const esc = s => escapeHtml(s);
  const pick = (e, attr) => { const t = e && e.target; return t && t.closest ? t.closest('[' + attr + ']') : null; };

  function cardHtml(c, size) { return '<span class="tc ' + SU[c.s] + (size ? ' ' + size : '') + '"><b>' + (c.r === 10 ? '10' : RK[c.r - 2]) + '</b><i>' + SYM[SU[c.s]] + '</i></span>'; }
  const backHtml = size => '<span class="tc back' + (size ? ' ' + size : '') + '"></span>';
  function feed(kind, html) {
    const f = $('trFeed'); if (!f) return null;
    const d = document.createElement('div');
    d.className = 'tr-msg' + (kind ? ' ' + kind : ''); d.innerHTML = plain(html);
    f.insertBefore(d, f.firstChild);
    while (f.children.length > 40) f.removeChild(f.lastChild);
    d.addEventListener('click', e => { if (!e.target.closest('button,a,input,select,summary')) d.classList.toggle('open'); });
    feedTog();
    return d;
  }
  // The notes so far stay folded away behind one button, so the column shows only the current explanation.
  function feedTog() {
    const f = $('trFeed'); if (!f) return;
    let b = f.previousElementSibling;
    if (!b || !b.classList.contains('tr-feedtog')) {
      b = document.createElement('button'); b.className = 'ghost tr-feedtog'; f.parentNode.insertBefore(b, f);
      b.onclick = () => { opts.feedOpen = !opts.feedOpen; saveOpts(); feedTog(); };
    }
    f.classList.toggle('open', !!opts.feedOpen);
    b.textContent = (opts.feedOpen ? '▾ Hide' : '▸ Show') + ' earlier notes (' + f.children.length + ')';
    b.style.display = f.children.length ? '' : 'none';
    if (opts.feedOpen) for (const d of f.children) d.classList.toggle('more', d.scrollHeight > d.clientHeight + 4);   // measurable only when shown
  }
  function tally(G) {
    stats[G.v] = (stats[G.v] || 0) + 1;
    if (G.street != null) { stats.byStreet = stats.byStreet || [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]; const row = stats.byStreet[G.street] || (stats.byStreet[G.street] = [0, 0, 0]); row[G.v === 'good' ? 0 : G.v === 'ok' ? 1 : 2]++; } stats.loss = Math.round((stats.loss + (G.loss || 0)) * 100) / 100;
    if (G.usd) stats.lossUsd = Math.round(((stats.lossUsd || 0) + G.usd) * 100) / 100;
    if (G.v === 'bad') { const key = (G.street != null ? STREET[G.street] + ' · ' : '') + G.head; stats.leaks[key] = (stats.leaks[key] || 0) + 1; }
    saveStats();
  }

  // ---- for the 🎯 Coach: the same engine on a spot read off another site ------------------------
  // s is a spot in the trainer's shape (street, pos, k, cards, board, pot, toCall, raises, curBet,
  // myBet, maxTo, openerPos, heroOpened, facingAllIn, opps), amounts in big blinds. Returns the best
  // play, a concrete size, and the explanation — the same words the trainer uses.
  function adviceForSpot(s) {
    let best, why, E = null;
    if (!s.street) { const A = preflopAdvice(s.k, s); best = A.best; why = A.why; }
    else {
      E = equityVsRanges(s.cards, s.board, s.opps, 2500, mulberry(seedOf(JSON.stringify([s.cards, s.board, s.pot, s.toCall]))));
      const kinds = s.toCall > 0 ? ['raise', 'call', 'fold'] : ['raise', 'check'];
      const rated = kinds.map(k => ({ k, G: gradePost(s, k, E) }));
      const b = pickBest(rated, s, E);
      best = b.k; why = b.G.why;
    }
    if (best === 'call' && s.toCall <= 0) best = 'check';
    if (s.posUnknown) why = 'Note: your seat was not read from the screen, so this treats it as the hijack (a middle seat).\n' + why;
    const dd = s.street ? draws(s.cards, s.board) : { outs: 0 };
    const adv = best === 'raise' ? sizeAdvice(s, E == null ? 50 : E, dd.outs >= 8 && s.street < 3) : null;
    let to = null;
    if (adv) {
      const mid = (adv.lo + adv.hi) / 2;
      to = adv.unit === 'bb' ? (s.pos === 'SB' ? 3 : 2.5) : adv.unit === 'x' ? mid * Math.max(s.curBet, 1) : s.myBet + mid * s.pot;
      to = Math.min(s.maxTo, Math.max(to, s.curBet + Math.max(1, s.curBet - 0)));   // never below a legal raise
      to = Math.round(to * 2) / 2;
    }
    const doTxt = best === 'raise' ? ((s.street ? (s.toCall > 0 ? 'Raise to ' : 'Bet ') : (s.raises === 0 ? 'Raise to ' : s.raises === 1 ? '3-bet to ' : '4-bet to ')) + (to != null ? bbs(to) : '')).trim()
      : best === 'call' ? 'Call ' + bbs(r2(s.toCall)) : best.charAt(0).toUpperCase() + best.slice(1);
    return { best, do: doTxt, to, E, why: why + (adv ? '\nBet size: ' + adv.rec + '. ' + adv.why : '') };
  }
  // Grade what the player actually did in that spot (the Coach records it like a trainer decision).
  function gradeForSpot(s, kind, to, E) {
    if (kind === 'raise' && !(to > s.curBet)) kind = 'call';
    if (kind === 'call' && s.toCall === 0) kind = 'check';
    if (kind === 'check' && s.toCall > 0) kind = 'fold';
    const EE = s.street ? (E == null ? equityVsRanges(s.cards, s.board, s.opps, 2500) : E) : null;
    return withSizing(s.street ? gradePost(s, kind, EE) : gradePre(s, kind), s, kind, Math.max(s.curBet, Number(to) || 0), EE);
  }
  // A coached decision on another site goes into the same record as a trainer decision (leaks, totals).
  function recordCoached(rec) {
    if (!rec || !rec.G) return;
    tally(rec.G); stats.coach = (stats.coach || 0) + 1; saveStats();
  }

  // ---- 🃏 Play — solo against bots, or a table with friends over the internet --------------------
  // A friends' table: the HOST's Poker Angel runs the game (deals, bots, grading) and sends each
  // player the table as they are allowed to see it; a guest only sends its own actions. Connections
  // are direct between the players' PCs (WebRTC data channels via PeerJS — its free public server
  // only introduces them). Seats without a person are bots; a friend who drops out becomes a bot.
  // The host chooses how much everyone sees while a hand is played:
  //   face up  — every card and every grade, as it happens (a teaching table)
  //   own only — your own cards and grades; everyone's are revealed when the hand ends, so no grade
  //              gives away a hand while it is still being played.
  const NAME_KEY = 'pokerangel.name', PEER_PREFIX = 'pokerangel-', NEXT_HAND_MS = 6000;
  // STUN finds a direct route; the free relay carries the data when there isn't one (a phone on mobile
  // data, a strict router). The PeerJS server only introduces the two ends.
  const PEER_OPTS = { config: { iceServers: [{ urls: 'stun:stun.l.google.com:19302' }, { urls: 'stun:stun1.l.google.com:19302' },
    { urls: ['turn:openrelay.metered.ca:80', 'turn:openrelay.metered.ca:443', 'turn:openrelay.metered.ca:443?transport=tcp'], username: 'openrelayproject', credential: 'openrelayproject' }] } };
  let me = 0;                       // my seat (-1 = watching until the next deal)
  // The explanation of my latest decision stays on the table until I press Continue (or Got it at a
  // friends' table). Solo, the bots wait for that press too — unless "Pause after each decision" is off.
  let ackId = null;
  // Play ratings for this table: how closely each person's choices match the best play. A choice that
  // matches scores 1, a close one 0.6, a different one 0; the rating is the average × 100. Built on
  // every screen from the decisions that screen can see (so with "own cards only", others' ratings
  // move when the hand ends).
  let ratings = {};
  function rateAdd(d) {
    const r = ratings[d.name] || (ratings[d.name] = { n: 0, pts: 0, loss: 0, usd: 0, seat: d.seat });
    r.n++; r.pts += d.G.v === 'good' ? 1 : d.G.v === 'ok' ? 0.6 : 0; r.loss += d.G.loss || 0; r.usd += d.G.usd || 0; r.seat = d.seat;
  }
  function ratingsBar() {
    const names = Object.keys(ratings); if (!names.length) return '';
    const rows = names.map(n => ({ n, r: ratings[n], score: Math.round(ratings[n].pts / ratings[n].n * 100) })).sort((a, b) => b.score - a.score || b.r.n - a.r.n);
    return '<div class="tr-ratings"><span class="tr-dim" title="How closely each player’s choices match the best play: 100 = every choice matched.">Play ratings</span>'
      + rows.map(x => '<span class="tr-rate' + (x.r.seat === me ? ' me' : '') + '"><b>' + esc(x.r.seat === me ? 'You' : x.n) + '</b><em>' + x.score + '</em><small>' + x.r.n + ' decision' + (x.r.n === 1 ? '' : 's')
        + (x.r.loss > 0.05 ? ' · cost ' + r1(x.r.loss) + ' big blinds' : '') + (x.r.usd > 0.005 ? ' · cost ' + usd(x.r.usd) : '') + '</small></span>').join('') + '</div>';
  }
  const pauseOn = () => opts.pause !== false;
  function myPending() {
    if (!g || me < 0) return null;
    const mine = visibleDecisions(me).filter(d => d.seat === me && d.id.indexOf(handKey() + '.') === 0);
    const d = mine[mine.length - 1];
    return d && d.id !== ackId ? d : null;
  }
  const holding = () => !room && !autoOn() && pauseOn() && !!myPending() && g && !g.over && !watchOn();
  // While you're in the hand (solo), each bot move waits for Next move ▶, so its comment box can be read.
  const stepBots = () => !room && !autoOn() && opts.stepBots !== false && g && !g.over && me >= 0 && g.players[me] && !g.players[me].folded && !g.players[me].out && !isHuman(g.players[g.toAct]);
  let room = null;                  // { role, code, peer, conns (host: Map conn → {seat,name,pending}), conn (guest), faceUp, players }
  const shownDec = new Set();       // decisions already in my feed
  let summarized = 0, introduced = 0;
  const myName = () => String(ls(NAME_KEY) || 'You').trim().slice(0, 16) || 'You';
  const isGuest = () => !!(room && room.role === 'guest');
  const isHost = () => !!(room && room.role === 'host');
  const r2 = v => Math.round(v * 100) / 100;
  const seedOf = str => { let h = 2166136261; for (let i = 0; i < str.length; i++) { h ^= str.charCodeAt(i); h = Math.imul(h, 16777619); } return h >>> 0; };
  const view = i => { const n = g ? g.players.length : NSEATS; return (i - Math.max(me, 0) + n) % n; };   // seat → position on screen (mine at the bottom)
  const cleanErr = e => String(e && e.message || e).replace(/^Error invoking remote method '[^']+': (Error: )?/, '');

  const handKey = () => (g.gid || '') + '#' + g.handNo;        // unique across games (a new tournament restarts at hand 1)
  function startHand() {
    if (isGuest()) return;
    roomSync(); chatterSchedule();
    if (g && g.tour && g.tour.done) return;
    if (!g) { g = newGame(Math.random, opts.field); g.players[0].name = room ? myName() : 'You'; }
    if (!g.tour) g.depth = opts.depth || 100;
    if (room) seatJoiners();
    // what a web guest needs to rebuild this hand: the table just before the deal, and the shuffle's seed
    g.start = { button: g.button, handNo: g.handNo, lastBB: g.lastBB, prevAlive: g.prevAlive, tour: g.tour ? JSON.parse(JSON.stringify(g.tour)) : null };
    g.seed = Math.floor(Math.random() * 4294967296) >>> 0;
    newHand(g, mulberry(g.seed)); decisions = []; token++; autoClose = '';
    onHandState();
    broadcast();
    step();
    showTable();
  }
  // One bot action, with its reason kept for watching (g.watchLog).
  function botMove() {
    const i = g.toAct, st = g.street, d = botDecide(g, i, Math.random);
    act(g, i, d);
    if (g.players[i].allin && !g.over) talkEvent('allin', { seat: i });
    const last = g.log.filter(l => l.i === i && l.kind !== 'post').pop();
    (g.watchLog || (g.watchLog = [])).push({ i, st, at: g.acts.length - 1, txt: last ? last.txt : d.type, why: d.why || '' });
  }
  // You folded (solo): the rest of the hand plays one action per Next, the bots' cards face up and each
  // move explained. Fast-fold, when on, skips it as before.
  const watchOn = () => !room && !autoOn() && opts.watch !== false && g && me >= 0 && g.players[me] && g.players[me].folded && !g.players[me].out;
  const watching = () => watchOn() && !g.over && !fastFolding();
  function watchPlay(all) {
    let guard = 0;
    do { if (!g || g.over || isHuman(g.players[g.toAct])) break; try { botMove(); } catch (e) { console.error('trainer bot', e); break; } } while (all && guard++ < 300);
    step();
  }
  function watchHtml() {
    if (!watchOn()) return '';
    const fold = g.acts.findIndex(a => a[0] === me && a[1] === 'fold');
    const line = w => { const p = g.players[w.i]; return '<div class="tr-why"><b class="tr-lbl">' + esc(plain(p.name + ' (' + posOf(g, w.i) + ') ' + w.txt)) + '</b> <span class="tr-dim">' + esc(cardsTxt(p.cards) + ' · ' + botLabel(p)) + '</span>\n' + esc(plain(w.why))
      + (STYLE_HOW[p.style] ? '\n<i class="tr-dim">How a ' + esc(styleName(p.style)) + ' player plays: ' + esc(STYLE_HOW[p.style]) + '</i>' : '') + '</div>'; };
    const log = g.watchLog || [], after = log.filter(w => w.at > fold), before = log.filter(w => w.at < fold);
    return '<div class="tr-explain tr-narrate"><b>👀 You folded — watch how the bots play it out</b>'
      + '<div class="tr-why">Their cards are face up now. Press <b>Next move ▶</b> under the table — each player’s reason appears in a box beside them.</div>'
      + (after.length ? '<details><summary>All moves since you folded (' + after.length + ')</summary>' + after.map(line).join('') + '</details>' : '')
      + (before.length ? '<details><summary>Why they played as they did before you folded (' + before.length + ')</summary>' + before.map(line).join('') + '</details>' : '')
      + '</div>';
  }
  // ---- 🎬 Watch the Angel play ----------------------------------------------------------------------
  // Sit back: the Angel takes your seat and plays hand after hand with the trainer's own best play —
  // every card face up, every move (its own and the bots') explained beside the player and in the
  // column, and read aloud. The loop paces itself: a move, its commentary, then — once the voice has
  // finished — the next; a finished hand lingers a little longer before the next deal. Nothing the
  // Angel does counts in your stats, and Stop hands the seat back mid-hand.
  let auto = null, autoClose = '';  // auto: { speed, timer, prevSpeak, … }; autoClose: the session's close, kept on screen until the next deal
  const autoOn = () => !!auto && !room;
  const AUTO_GAP = { slow: 3200, normal: 1600, fast: 600 }, AUTO_MOVE = { slow: 6500, normal: 3800, fast: 1500 }, AUTO_HAND_END = 2500;
  const autoGap = () => (auto.calm ? 2200 : 0) + (CAN_TALK() && opts.speak ? AUTO_GAP[auto.speed] : AUTO_MOVE[auto.speed]);
  const AUTO_MINS = [0, 10, 20, 30, 45, 60];
  const minsLeft = () => auto && auto.endAt ? Math.max(0, Math.ceil((auto.endAt - Date.now()) / 60000)) : 0;
  // Run for… and 🌙 Sleep story. Shown in the Play menu and again in the Angel's column while it plays.
  function autoOptsHtml() {
    const cur = opts.autoMins || 0;
    return '<span class="tr-dim">⏱ Run for:</span>' + AUTO_MINS.map(m => '<button class="' + (m === cur ? 'primary' : 'ghost') + ' tr-mini" data-act="play:automins" data-v="' + m + '">' + (m ? m + ' min' : 'until I stop') + '</button>').join('')
      + '<label title="A slower, lower, softer voice and an unhurried pace — the same full explanations, told gently enough to drift off to. Ends quietly when the time is up."><input type="checkbox" data-opt="autoCalm"' + (opts.autoCalm ? ' checked' : '') + ' /> 🌙 Sleep story: calm voice, slow pace</label>';
  }
  const AUTO_BTN = '<button class="ghost" data-act="play:auto" title="The Angel plays your seat hand after hand — every card face up, every move explained and read aloud. Press Stop to take the seat back.">🎬 Let the Angel play</button>';
  const autoBar = () => '<span class="tr-wait">' + (auto.calm ? '🌙' : '🎬') + ' The Angel is playing — every card face up, every move explained' + (CAN_SPEAK ? ' and read aloud' : '') + (auto.endAt && !auto.done ? ' · ' + minsLeft() + ' min left' : '') + '.</span><button class="ghost" data-act="play:autostop">⏹ Stop — I’ll play</button>';
  // Start a sleep story (calm voice, slow pace) or a plain Angel run of n minutes — from a launch option.
  function sleepStory(mins, calm) {
    if (room) leaveRoom(true);
    if (auto) autoStop(true);
    opts.autoMins = Math.max(0, Math.round(Number(mins) || 0)); opts.autoCalm = calm !== false; opts.speak = true; saveOpts();
    if (!shown) open();
    setTab('play');
    autoStart();
  }
  function autoStart() {
    if (room || auto) return;
    auto = { speed: opts.autoCalm ? 'slow' : (opts.autoSpeed || 'normal'), timer: 0, prevSpeak: opts.speak, t0: Date.now(),
      endAt: opts.autoMins ? Date.now() + opts.autoMins * 60000 : 0, calm: !!opts.autoCalm, hands: 0, lessons: [], lesson: '', intro: true, done: false };
    if (CAN_TALK()) opts.speak = true;
    spokenLast = ''; said = new Set(); ackId = null; token++;
    if (!g || g.over) { if (g && g.tour && g.tour.done) freshTable(); startHand(); }
    if (g && g.players[me]) g.players[me].name = 'Angel';
    if (g) step();
    toast('🎬 The Angel is playing — press Stop whenever you want the seat back', 'green');
  }
  function autoStop(silent) {
    if (!auto) return;
    clearTimeout(auto.timer);
    opts.speak = auto.prevSpeak; auto = null; hush(); token++;
    if (g && g.players[me] && g.players[me].name === 'Angel') g.players[me].name = 'You';
    if (silent) return;
    toast('The seat is yours again', '');
    if (shown && tab === 'play') { renderPlay(); step(); }
  }
  // Wait for the commentary to be read (if the voice is on), then a pause for it to sink in, then move.
  function autoSchedule() {
    if (!auto) return;
    clearTimeout(auto.timer);
    const t0 = Date.now(), talk = CAN_TALK() && opts.speak, over = !!(g && g.over);
    let seen = false, endAt = 0;
    const tick = () => {
      if (!auto) return;
      if (!g) { autoStop(true); return; }
      const now = Date.now();
      if (!shown || tab !== 'play') { auto.timer = setTimeout(tick, 500); return; }       // paused while you're elsewhere; carries on when you're back
      const speaking = talk && voiceBusy(), queued = talk && !speaking && voiceQueued();
      if (speaking) { seen = true; endAt = 0; if (now - t0 < 60000) { auto.timer = setTimeout(tick, 200); return; } }
      if (queued && now - t0 < 4000) { auto.timer = setTimeout(tick, 200); return; }         // queued, not started yet
      if (queued) hush();                                                                      // the voice has stalled: clear it and carry on
      if (talk && !seen && !queued && now - t0 < 2500) { auto.timer = setTimeout(tick, 200); return; }   // give the voice time to start
      if (!endAt) endAt = now + autoGap() + (over ? AUTO_HAND_END + (auto.calm ? 2500 : 0) : 0);
      if (now < endAt) { auto.timer = setTimeout(tick, Math.min(250, endAt - now)); return; }
      autoTick();
    };
    auto.timer = setTimeout(tick, 50);
  }
  // One move: the Angel's (the trainer's recommended play, with its reasons kept for the column) or a bot's.
  function autoTick() {
    if (!auto) return;
    if (!g) { autoStop(true); return; }
    if (me < 0 || !g.players[me] || g.players[me].out) { autoStop(); return; }
    if (auto.done) { autoClose = autoHtml(); autoStop(true); renderPlay(); return; }
    if (g.over) {
      if (g.tour && g.tour.done) { autoStop(); return; }
      if (auto.endAt && Date.now() >= auto.endAt) { auto.done = true; hush(); spokenLast = ''; renderPlay(); autoSchedule(); return; }   // the close is read, then the seat is yours
      auto.hands++; auto.intro = false; startHand(); return;
    }
    if (g.toAct === me) {
      const a = adviceNow(), o = a && a.list.find(x => x.best);
      const kind = o ? o.kind : 'fold', to = o ? o.to : 0;
      (g.watchLog || (g.watchLog = [])).push({ i: me, st: g.street, at: g.acts.length, txt: '', why: a ? a.why : '', head: a ? a.do : 'Fold' });
      const rem = a && String(a.why).split('\n').find(l => /^Remember:/.test(l));
      if (rem) { auto.lesson = rem.replace(/^Remember:\s*/, ''); auto.lessonHand = g.handNo; if (auto.lessons.indexOf(auto.lesson) < 0) auto.lessons.push(auto.lesson); }
      doAct(me, kind, to);
      const w = g.watchLog[g.watchLog.length - 1], last = g.log.filter(l => l.i === me && l.kind !== 'post').pop();
      if (w && last && !w.txt) { w.txt = last.txt; renderPlay(); }
      return;
    }
    try { botMove(); } catch (e) { console.error('trainer bot', e); autoStop(); return; }
    step();
  }
  // The column while the Angel plays: the latest move and why, the hand so far (not read aloud), and the controls.
  function autoHtml() {
    if (!autoOn() || !g) return '';
    const log = g.watchLog || [], w = log[log.length - 1], hero = g.players[me];
    let body;
    if (auto.done) {
      const mins = Math.max(1, Math.round((Date.now() - auto.t0) / 60000)), n = auto.hands + (g.over ? 1 : 0);
      // (this block is also what autoClose keeps once the Angel has stopped)
      body = '<div class="tr-why"><b class="tr-lbl">That’s the end of this session.</b><span class="tr-nosay"> ' + n + ' hand' + (n === 1 ? '' : 's') + ' in ' + mins + ' minute' + (mins === 1 ? '' : 's') + '.</span></div>'
        + (auto.lessons.length ? '<div class="tr-why"><b class="tr-lbl">What to keep from tonight:</b>\n' + esc(plain(auto.lessons.slice(-6).map((l, k) => (k + 1) + '. ' + l).join('\n'))) + '</div>' : '')
        + '<div class="tr-why">' + (auto.calm ? 'Sleep well. The seat is yours whenever you come back.' : 'The seat is yours again.') + '</div>';
    } else if (g.over && g.result) {
      body = '<div class="tr-why"><b class="tr-lbl">Hand over.</b> ' + esc(plain(g.result.wins.map(x => (x.i === me ? 'The Angel wins ' : g.players[x.i].name + ' wins ') + bbs(r2(x.amt)) + (x.name ? ' with ' + x.name : '')).join(' · ')))
        + (g.result.showdown ? '.' : ' — everyone else folded.') + '</div>'
        + (auto.lesson && auto.lessonHand === g.handNo ? '<div class="tr-why"><b class="tr-lbl">Lesson from this hand:</b> ' + esc(plain(auto.lesson)) + '</div>' : '')
        + '<div class="tr-dim tr-nosay">Next hand in a moment…</div>';
    } else if (w) {
      const p = g.players[w.i], who = w.i === me ? 'The Angel' : p.name;
      body = '<div class="tr-why"><b class="tr-lbl">' + esc(plain(who + ' (' + posOf(g, w.i) + ') ' + w.txt)) + '</b> <span class="tr-dim">' + esc(cardsTxt(p.cards) + (w.i === me ? '' : ' · ' + botLabel(p))) + '</span></div>'
        + (w.i === me ? '<div class="tr-why">' + fmtWhy(w.why) + '</div>'
          : '<div class="tr-why">' + esc(plain(levelWhy(w.why))) + (STYLE_HOW[p.style] ? '\n<i class="tr-dim">How a ' + esc(styleName(p.style)) + ' player plays: ' + esc(STYLE_HOW[p.style]) + '</i>' : '') + '</div>');
    } else body = (auto.intro ? '<div class="tr-why tr-nosay">' + (auto.calm ? 'Settle in. ' : '') + 'The Angel plays hand after hand in your seat, every card face up, and explains each move — its own and the bots’ — with the numbers and the reasons.' + (auto.endAt ? ' It will play for ' + opts.autoMins + ' minutes and then close quietly.' : '') + '</div>' : '')
      + '<div class="tr-why">' + esc(plain('New hand. The Angel is in the ' + posOf(g, me) + ' with ' + (hero && hero.cards && hero.cards.length ? cardsTxt(hero.cards) : 'no cards yet') + '.')) + '</div>';
    const sp = v => '<button class="' + (auto.speed === v ? 'primary' : 'ghost') + ' tr-mini" data-act="play:autospeed" data-v="' + v + '">' + v + '</button>';
    if (auto.done) return '<div class="tr-advice tr-auto"><b>' + (auto.calm ? '🌙' : '🎬') + ' The Angel’s session</b>' + body + '</div>';
    return '<div class="tr-advice tr-auto"><b class="tr-nosay">' + (auto.calm ? '🌙' : '🎬') + ' The Angel plays · hand #' + g.handNo + (auto.endAt && !auto.done ? ' · ' + minsLeft() + ' min left' : '') + '</b>' + body
      + '<div class="tr-row tr-nosay"><button class="ghost tr-mini" data-act="play:autostop">⏹ Stop — I’ll play</button><span class="tr-dim">Pace:</span>' + sp('slow') + sp('normal') + sp('fast') + '</div>'
      + '<div class="tr-row tr-nosay">' + autoOptsHtml() + '</div></div>'
      + '<div class="tr-nosay">' + storyHtml(g, me, true) + '</div>';
  }

  // On a phone the page scrolls as a whole, and the Play menu is long — so when a hand is dealt the
  // table might sit below where the player was looking. Bring it into view.
  function showTable() {
    try { if (window.innerWidth < 760) { const el = document.querySelector('.tr-felt-wrap'); if (el) el.scrollIntoView({ behavior: 'smooth', block: 'start' }); } } catch (e) {}
  }
  // Bots act on the host (or solo). A person's turn waits for them.
  function step() {
    if (tab === 'play') renderPlay(); else renderSpot();
    if (!g || isGuest()) return;
    if (g.over) { if (!g._done) handEnd(); if (autoOn()) autoSchedule(); return; }
    if (autoOn()) { autoSchedule(); return; }                     // 🎬 the Angel's loop paces every move (its own and the bots')
    if (isHuman(g.players[g.toAct])) return;
    if (holding()) return;                                        // waiting for me to press Continue
    if (watching()) return;                                       // you folded: each move waits for Next
    if (stepBots()) return;                                       // you're in: each bot move waits for Next too
    if (fastFolding()) {                                          // you've left this hand: the rest plays out at once
      let guard = 0;
      while (!g.over && guard++ < 300) { try { botMove(); } catch (e) { break; } }
      return step();
    }
    const tok = ++token, fast = g.players.every(p => !isHuman(p) || p.folded);
    setTimeout(() => {
      // Solo, the bots wait while you're in a drill or the coach (acting would redraw a drill and wipe
      // what you typed); setTab('play') / open() pick the hand back up. At a friends' table the game
      // must go on for everyone, so it never pauses.
      if (tok !== token || !g || g.over || isHuman(g.players[g.toAct]) || holding()) return;
      if (!room && (!shown || tab !== 'play')) return;
      try { botMove(); } catch (e) { console.error('trainer bot', e); return; }
      broadcast();
      step();
    }, fast ? BOT_MS_FAST : BOT_MS);
  }
  // Grade a person's decision, record it, then play it.
  function gradeAndAct(i, type, to) {
    const s = spot(g, i), L = legal(g, i);
    let kind = type;
    if (kind === 'raise' && (!L.canRaise || !(to > g.curBet))) kind = 'call';
    if (kind === 'call' && L.toCall === 0) kind = 'check';
    if (kind === 'check' && L.toCall > 0) kind = 'fold';
    const E = s.street ? equityVsRanges(s.cards, s.board, s.opps, 2500, mulberry(seedOf(handKey() + '/' + (g.acts || []).length))) : null;
    if (i === me && s.street && s.toCall <= 0 && E != null) {                   // a bluffing opportunity: nothing much, nobody has bet
      const th = thresholds(s), d = draws(s.cards, s.board);
      if (E / 100 < th.vt && d.outs < 8) { stats.bluffOps = (stats.bluffOps || 0) + 1; if (kind === 'raise') stats.bluffs = (stats.bluffs || 0) + 1; }
    }
    if (i === me && !autoOn()) { const sc = tableLessonScore(s, kind, E); if (sc) { stats.tableLesson = stats.tableLesson || {}; const F = FIELDS[opts.field || 'mixed'], t = stats.tableLesson[F.lesson] = stats.tableLesson[F.lesson] || { good: 0, bad: 0, last: '' }; if (sc.v > 0) t.good++; else t.bad++; t.last = sc.note; saveStats(); } }
    const short = !s.street && gradeShort(g, i, kind, to);
    const G = short || withSizing(s.street ? gradePost(s, kind, E) : gradePre(s, kind), s, kind, Math.max(L.minTo, Math.min(L.maxTo, half(Number(to) || 0))), E);
    const live = g.players.filter((q, j) => j !== i && !q.folded);
    const Eact = (room || opts.showBots) && live.length ? equityVsRanges(s.cards, s.board, live.map(q => ({ fixed: q.cards })), 2000) : null;
    G.street = s.street;
    decisions.push({ id: handKey() + '.' + decisions.length, at: (g.acts || []).length, seat: i, name: g.players[i].name, street: s.street, kind, verb: verbOf(kind, s), G, E, Eact, detail: detailFor(g, i, E), auto: autoOn() && i === me });
    act(g, i, { type: kind, to });
    if (g.players[i].allin && !g.over) talkEvent('allin', { seat: i });
  }
  // Runs on the host (or solo) for every person's action.
  function doAct(i, type, to) {
    if (!g || g.over || g.toAct !== i) return;
    gradeAndAct(i, type, to);
    onHandState();
    broadcast();
    step();
  }
  function heroAct(type, to) {
    if (!g || g.over || me < 0 || g.toAct !== me) return;
    if (isGuest() && room.web) {                                 // claude.ai: the move goes in my presence for the host to play
      room.sent = handKey() + '/' + g.acts.length;
      room.r.presence({ act: { k: handKey(), n: g.acts.length, type, to: Number(to) || 0 } }).catch(() => toast('Couldn’t reach the table', 'red'));
      renderPlay();
      return;
    }
    if (isGuest()) {
      try { room.conn.send({ t: 'act', handNo: g.handNo, type, to }); } catch (e) { toast('Lost the connection to the table', 'red'); return; }
      g.toAct = -1; renderPlay();                                 // until the host's update arrives
      return;
    }
    doAct(me, type, to);
  }
  // ---- advice before you act ----
  // Worked out once per decision (the equity simulation is the slow part) and kept until I act.
  let _advice = null;
  function sizeVerdict(s, to, adv) {
    if (!adv) return '';
    const allIn = to >= s.maxTo - 0.01;
    if (allIn) return s.maxTo <= 25 ? 'With a short stack, all-in is a natural size.' : 'Puts your whole stack at risk — far bigger than this spot needs.';
    const val = adv.unit === 'bb' ? to : adv.unit === 'x' ? to / Math.max(s.curBet, 1e-9) : (to - s.myBet) / Math.max(s.pot, 1e-9);
    return val < adv.lo - 1e-9 ? 'Smaller than the usual size (' + adv.rec + ').' : val > adv.hi + 1e-9 ? 'Bigger than the usual size (' + adv.rec + ').' : 'The recommended size.';
  }
  // Among the plays graded good, the one the maths favours: a bet only when clearly ahead of the
  // betting line, a raise over a call only when well ahead; otherwise the quieter play.
  function pickBest(rated, s, E) {
    const good = rated.filter(r => r.G.v === 'good');
    if (good.length > 1) {
      const e = (E == null ? 50 : E) / 100, th = thresholds(s);
      if (s.toCall <= 0) return (e >= th.vt + 0.06 ? good.find(r => r.k === 'raise') : null) || good.find(r => r.k === 'check') || good[0];
      return (e >= th.rt + 0.05 ? good.find(r => r.k === 'raise') : null) || good.find(r => r.k === 'call') || good[0];
    }
    return good[0] || rated.find(r => r.G.v === 'ok') || rated[0];
  }
  function adviceNow() {
    if (!g || g.over || me < 0 || g.toAct !== me) return null;
    const key = handKey() + '/' + (g.acts || []).length;
    if (_advice && _advice.key === key) return _advice;
    const s = spot(g, me), L = legal(g, me), p = g.players[me], sp = !s.street && shortSpot(g, me);
    let best, why, E = null, view = null;
    if (sp) {
      const go = gradeShort(g, me, sp.type === 'shove' ? 'raise' : 'call', p.bet + p.stack);
      best = go.v === 'good' ? (sp.type === 'shove' ? 'raise' : 'call') : 'fold'; why = go.why;
    } else if (!s.street) {
      const A = preflopAdvice(s.k, s); best = A.best; why = A.why; view = A.view;
    } else {
      E = equityVsRanges(s.cards, s.board, s.opps, 2500, mulberry(seedOf(key)));   // the same draw for the same spot: the figure doesn't wander between views
      const kinds = s.toCall > 0 ? ['raise', 'call', 'fold'] : ['raise', 'check'];
      const rated = kinds.map(k => ({ k, G: gradePost(s, k, E) }));
      const b = pickBest(rated, s, E);
      best = b.k; why = b.G.why;
    }
    const dd = s.street ? draws(s.cards, s.board) : { outs: 0 };
    const adv = sp ? null : sizeAdvice(s, E == null ? 50 : E, dd.outs >= 8 && s.street < 3);
    const list = [];
    list.push({ kind: 'fold', label: 'Fold', note: L.toCall > 0 ? 'Give up the hand and the chips you’ve already put in.' : 'Never needed here — checking is free.' });
    if (L.toCall > 0) {
      const need = r1(L.toCall / (L.pot + L.toCall) * 100);
      list.push({ kind: 'call', label: 'Call ' + bbs(L.toCall), note: 'You need to win at least ' + need + '% of the time to break even' + (E != null ? '; you have about ' + E + '%.' : '.') });
    } else list.push({ kind: 'check', label: 'Check', note: 'Free: see the next card (or the showdown) without putting more in.' });
    if (L.canRaise) for (const z of sizes()) list.push({ kind: 'raise', label: z.label, to: z.to, note: sp ? (z.to >= L.maxTo - 0.01 ? 'All-in: the push/fold play at this stack.' : 'A smaller raise — at this stack, all-in or fold is better.') : sizeVerdict(s, z.to, adv) });
    for (const o of list) o.best = o.kind === best && (o.kind !== 'raise' || sp ? (o.kind !== 'raise' || o.to >= L.maxTo - 0.01) : /recommended/.test(o.note));
    if (best === 'raise' && !list.some(o => o.best)) { const r = list.filter(o => o.kind === 'raise'); if (r.length) r[0].best = true; }
    const detail = detailFor(g, me, E);
    const pickd = list.find(o => o.best), m = pickd && /^(.+?) · (\S+)$/.exec(pickd.label);
    const doTxt = !pickd ? best : m ? 'Bet ' + m[2] + ' (' + m[1] + ')' : pickd.label;        // "¾ pot · 6bb" → "Bet 6bb (¾ pot)"; "Raise to 2.5bb"; "Call 3bb"; "Check"; "Fold"
    _advice = { key, detail, do: doTxt, view, k: s.k, best: best === 'raise' ? (sp ? 'all-in' : verbOf('raise', s) + (adv ? ' (' + adv.rec + ')' : '')) : best, why: why + (adv && best === 'raise' ? '\nBet size: ' + adv.rec + '. ' + adv.why : ''), list };
    return _advice;
  }
  const Trainer_g = () => g, Trainer_me = () => me;
  // ---- what has happened so far this hand, for the moment it's your turn ----
  // Street by street from the log: runs of folds collapsed, you named "You", the board as it came out,
  // then the pot, who's still in and what you're facing — so the decision can be read without
  // scanning the table.
  function storyHtml(G, M, force) {
    const g = G || Trainer_g(), me = M == null ? Trainer_me() : M;   // the live hand unless a test passes one in
    if (!g || g.over || me < 0 || (!force && g.toAct !== me)) return '';
    const angel = autoOn(), mine = g.toAct === me;
    const name = i => i === me ? (angel ? 'The Angel' : 'You') : g.players[i].name + ' (' + posOf(g, i) + ')';
    const verb = l => l.i === me && !angel ? l.txt.replace(/^(posts|folds|calls|checks|bets|raises)/, (_, v) => ({ posts: 'post', folds: 'fold', calls: 'call', checks: 'check', bets: 'bet', raises: 'raise' }[v])) : l.txt;
    const streets = [];
    for (let st = 0; st <= g.street; st++) {
      const acts = g.log.filter(l => l.st === st && l.kind !== 'post');
      const b = st === 1 ? g.board.slice(0, 3) : st === 2 ? g.board.slice(0, 4) : st === 3 ? g.board : [];
      const parts = [];
      for (let k = 0; k < acts.length; k++) {
        if (acts[k].kind === 'fold' && acts[k].i !== me) {                       // "3 fold" instead of three names
          let n = 0; while (k + n < acts.length && acts[k + n].kind === 'fold' && acts[k + n].i !== me) n++;
          parts.push(n === 1 ? name(acts[k].i) + ' folds' : n + ' fold');
          k += n - 1;
        } else parts.push(name(acts[k].i) + ' ' + verb(acts[k]));
      }
      if (!parts.length && st === g.street) parts.push(mine ? (angel ? 'The Angel acts first.' : 'You act first.') : 'No action yet.');
      streets.push('<div><b class="tr-lbl">' + STREET[st] + (b.length ? ' ' + b.map(c => cardHtml(c)).join('') : '') + '</b> ' + esc(plain(parts.join(' · '))) + (parts.length && !/\.$/.test(parts[parts.length - 1]) ? '.' : '') + '</div>');
    }
    const L = legal(g, me), live = g.players.filter((q, j) => j !== me && !q.folded && !q.out).length;
    const facing = !mine ? (g.toAct >= 0 ? g.players[g.toAct].name + ' to act' : '') : L.toCall > 0 ? 'Facing ' + bbs(L.toCall) + ' to call' + (g.players.filter(q => q.allin && !q.folded).length ? ' (someone is all-in)' : '') : 'No bet to ' + (angel ? 'the Angel' : 'you');
    const now = 'Pot ' + bbs(r2(L.pot)) + ' · ' + live + ' opponent' + (live === 1 ? '' : 's') + ' still in' + (facing ? ' · ' + facing : '') + '.';
    return '<div class="tr-explain tr-story"><b>📜 So far this hand</b>' + streets.join('') + '<div class="tr-now">' + esc(plain(now)) + '</div></div>';
  }
  function adviceHtml() {
    const a = adviceNow(); if (!a) return '';
    return '<div class="tr-advice"><b>' + esc(plain('Your turn · ' + a.do)) + '</b><div class="tr-why">' + fmtWhy(a.why) + '</div>' + chartMini(a.view, a.k) + detailHtml(a.detail, true)
      + '<div class="tr-optlist"><span class="tr-dim">Your options:</span>' + a.list.map(o => '<div class="tr-opt' + (o.best ? ' best' : '') + '"><b>' + esc(plain(o.label)) + '</b>' + (o.best ? '<span class="tr-tag">Recommended</span>' : '') + '<span>' + esc(plain(o.note)) + '</span></div>').join('') + '</div></div>';
  }
  function hint() {
    if (!g || g.over || me < 0 || g.toAct !== me) return;
    const s = spot(g, me); stats.hints++; saveStats();
    if (!s.street && shortSpot(g, me)) {
      const p = g.players[me], sp = shortSpot(g, me), aggr = gradeShort(g, me, sp.type === 'shove' ? 'raise' : 'call', p.bet + p.stack);
      const lean = aggr.v === 'good' ? (sp.type === 'shove' ? 'shove' : 'call') : 'fold';
      feed('', '<b>💡 Hint: ' + (lean === 'shove' ? 'all-in' : lean) + '</b>' + fmtWhy(aggr.why)); return;
    }
    if (!s.street) { const A = preflopAdvice(s.k, s), adv = A.best === 'raise' ? sizeAdvice(s, 50, false) : null; feed('', '<b>💡 Hint: ' + esc(verbOf(A.best, s)) + (adv ? ' to ' + esc(adv.rec) : '') + '</b>' + fmtWhy(A.why + (adv ? '\nBet size: ' + adv.rec + '. ' + adv.why : '') + (g.tour && effStack(g, me) < 60 ? '\nNote: the charts are for 100 big blinds. With ' + r1(effStack(g, me)) + ' big blinds, play a little tighter and avoid just calling raises.' : ''))); return; }
    const E = equityVsRanges(s.cards, s.board, s.opps, 2500, mulberry(seedOf(handKey() + '/' + (g.acts || []).length)));
    const kinds = s.toCall > 0 ? ['raise', 'call', 'fold'] : ['raise', 'check'];
    const rated = kinds.map(k => ({ k, G: gradePost(s, k, E) }));
    const best = pickBest(rated, s, E);
    const dd = draws(s.cards, s.board), adv = best.k === 'raise' ? sizeAdvice(s, E, dd.outs >= 8 && s.street < 3) : null;
    feed('', '<b>💡 Hint: ' + esc(verbOf(best.k, s)) + (adv ? ' ' + esc(adv.rec) : '') + '</b>' + fmtWhy(best.G.why + (adv ? '\nBet size: ' + adv.rec + '. ' + adv.why : '')));
  }
  // Which decisions a seat may see now: all of them at a face-up table or once the hand is over;
  // otherwise only their own, without the "against the actual cards" figure (that would give
  // the others' hands away).
  function visibleDecisions(seat) {
    if (!room || room.faceUp || (g && g.over)) return decisions;
    return decisions.filter(d => d.seat === seat).map(d => Object.assign({}, d, { Eact: null }));
  }
  // The chart a preflop decision was graded against, with this hand marked — the same grid as the Charts tab.
  function chartMini(view, k) {
    if (!view || !VIEWS.some(v => v.id === view)) return '';
    return '<details class="tr-chartmini" open><summary>The chart for this spot — your hand is outlined</summary>' + gridHtml(view, k || '') + legendHtml(view) + '</details>';
  }
  function decHtml(d, toggle) {
    const who = d.seat === me ? 'You' : d.name;
    return '<b>' + esc(plain(who + ' chose: ' + (d.verb || d.kind) + ' · ' + d.G.head)) + '</b><div class="tr-why">' + fmtWhy(d.seat === me ? d.G.why.split('\n').filter(l => !/^Your hand:/.test(l)).join('\n') : d.G.why) + '</div>' + (d.street === 0 ? chartMini(d.G.view, d.G.k) : '') + detailHtml(d.detail, toggle) + '<div class="tr-why">'
      + (d.Eact != null ? '\nAgainst the cards actually held: ' + d.Eact + '%.' : '')
      + (d.G.loss > 0 && d.kind !== d.G.head.replace(/^Best play: (\w+).*/, '$1') ? '\nWhat this choice costs: about ' + bbs(d.G.loss) + ' each time, on average.' : '')
      + (d.G.usd > 0 ? '\nWhat this choice costs: about ' + usd(d.G.usd) + ' in prize money, on average.' : '')
      + '</div><small>' + STREET[d.street] + ' · ' + esc(who) + ' ' + esc(d.verb || d.kind) + '</small>';
  }
  // Everything that follows a change of the hand, the same on every PC: new-hand note, newly visible
  // grades into the feed (and my own into my stats), the summary when it ends.
  function onHandState() {
    if (!g || !g.handNo) return;
    if (introduced !== handKey()) {
      introduced = handKey();
      const p = g.players[me], T = g.tour;
      if (T && g.handNo === 1) feed('', '<b>🏆 Tournament started</b>' + esc(tourLine(g)) + '\nPrizes: ' + T.payouts.map((v, k) => ordinal(k + 1) + ' $' + v).join(' · ') + ' (pool $' + T.pool + ').');
      if (me >= 0 && p && p.cards && p.cards.length) feed('', '<b>Hand #' + g.handNo + (T ? ' · Level ' + (T.level + 1) : '') + '</b>' + (autoOn() ? 'The Angel is' : 'You are') + ' in the ' + posOf(g, me) + ' with ' + esc(cardsTxt(p.cards)) + ' (' + cls(p.cards[0], p.cards[1]) + ')' + (T ? ', ' + r1(p.stack + p.bet) + 'bb.' : '.'));
      else if (!(T && p && p.out)) feed('', '<b>Hand #' + g.handNo + '</b>Watching — you’re dealt in from the next ' + (T ? 'game.' : 'hand.'));
    }
    for (const d of visibleDecisions(me)) {
      if (shownDec.has(d.id)) continue;
      shownDec.add(d.id);
      if (d.seat === me && !d.auto) tally(d.G);              // the Angel's own play isn't your record
      rateAdd(d);
      feed('', decHtml(d));
    }
    if (g.over && summarized !== handKey()) summarize();
  }
  const ordinal = n => n + (n % 10 === 1 && n % 100 !== 11 ? 'st' : n % 10 === 2 && n % 100 !== 12 ? 'nd' : n % 10 === 3 && n % 100 !== 13 ? 'rd' : 'th');
  const blindsTxt = T => { const bb = T.levels[T.level]; return (bb / 2).toLocaleString() + '/' + bb.toLocaleString() + ' + ' + bb.toLocaleString() + ' ante'; };
  function tourLine(g) {
    const T = g.tour, left = T.chips.filter(c => c > 0).length;
    return 'Level ' + (T.level + 1) + ' · blinds ' + blindsTxt(T) + ' · ' + (T.perLevel - T.handsAt) + ' hand' + (T.perLevel - T.handsAt === 1 ? '' : 's') + ' to the next level · ' + left + ' left · ' + T.payouts.length + ' paid';
  }
  // ---- hand history (from PokerStars' hand replayer): your last 30 hands, replayable step by step ----
  const HIST_KEY = 'pokerangel.hands';
  let history = [];
  try { history = JSON.parse(ls(HIST_KEY) || '[]') || []; } catch (e) { history = []; }
  function saveHand() {
    if (!g || g.seed == null || !g.start || me < 0 || !g.players[me] || !g.players[me].cards || !g.players[me].cards.length) return;
    const p = g.players[me];
    const rec = { id: handKey(), when: Date.now(), handNo: g.handNo, me, tour: !!g.tour,
      seats: g.players.map(q => ({ n: q.name, s: q.style || null, l: q.level || null })),
      start: g.start, seed: g.seed, acts: (g.acts || []).slice(),
      cards: cardsTxt(p.cards), k: cls(p.cards[0], p.cards[1]), pos: posOf(g, me), net: r2(p.stack - (g.startStacks ? g.startStacks[me] : 100)),
      dec: decisions.map(d => ({ seat: d.seat, name: d.name, street: d.street, kind: d.kind, verb: d.verb, at: d.at, Eact: d.Eact, detail: d.detail || null, G: { v: d.G.v, head: d.G.head, why: d.G.why, loss: d.G.loss, usd: d.G.usd, view: d.G.view || null, k: d.G.k || null } })) };
    history = [rec].concat(history.filter(h => h.id !== rec.id)).slice(0, 30);
    try { ls(HIST_KEY, JSON.stringify(history)); } catch (e) {}
  }
  // Rebuild a saved hand up to a given action (the same replay the web friends' table uses).
  function replayGame(rec, steps) {
    const rg = { players: rec.seats.map(x => ({ name: x.n, style: x.s, level: x.l })), button: rec.start.button, handNo: rec.start.handNo, gid: 'replay' };
    if (rec.start.tour) rg.tour = JSON.parse(JSON.stringify(rec.start.tour));
    rg.lastBB = rec.start.lastBB; rg.prevAlive = rec.start.prevAlive;
    newHand(rg, mulberry(rec.seed));
    for (let k = 0; k < steps && k < rec.acts.length; k++) { const [i, kind, to] = rec.acts[k]; if (rg.over || rg.toAct !== i) break; act(rg, i, { type: kind, to }); }
    return rg;
  }
  // From a decision the grade marked wrong: replace that one action with the best play, let the bots
  // play on (and the hero follow the trainer's advice thereafter), and show how it goes. Built only
  // from the saved seed and actions, so it is the same deal every time.
  function whatIf(rec, d) {
    const rg = replayGame(rec, d.at), me0 = rec.me; if (rg.over || rg.toAct !== me0) return null;
    const bestWord = (String(d.G.head).match(/^Best play: ([a-z0-9()\- ]+?)(?: —|$)/i) || [])[1] || '';
    const s0 = spot(rg, me0), L0 = legal(rg, me0);
    let kind = /fold/i.test(bestWord) ? 'fold' : /check/i.test(bestWord) ? 'check' : /call/i.test(bestWord) ? 'call' : 'raise', to = 0;
    if (kind === 'raise') { const a0 = adviceForSpot(s0); to = /all-in/i.test(bestWord) ? L0.maxTo : (a0.to || L0.minTo); }
    if (kind === 'check' && L0.toCall > 0) kind = 'call';
    const seq = []; const name = j => j === me0 ? 'You' : rg.players[j].name;
    const doit = (j, a) => { act(rg, j, a); const last = rg.log[rg.log.length - 1]; seq.push(name(j) + ' (' + last.pos + ') ' + last.txt); };
    doit(me0, { type: kind, to });
    const rng = mulberry((rec.seed >>> 0) + 7); let guard = 0;
    while (!rg.over && guard++ < 200) {
      const j = rg.toAct;
      if (j === me0) { const a = adviceForSpot(spot(rg, me0)); const L = legal(rg, me0); let k2 = a.best === 'check' && L.toCall > 0 ? 'call' : a.best; doit(me0, { type: k2, to: a.to || L.minTo }); }
      else doit(j, botDecide(rg, j, rng));
    }
    const net = r2(rg.players[me0].stack - (rec.start.tour ? rg.startStacks[me0] : (rg.startStacks ? rg.startStacks[me0] : 100)));
    const result = rg.result ? rg.result.wins.map(w => name(w.i) + ' win' + (w.i === me0 ? '' : 's') + ' ' + bbs(r2(w.amt)) + (w.name ? ' — ' + w.name : '')).join('; ') : '';
    return { kind, to, seq, result, net, board: rg.board.slice() };
  }
  function whatIfHtml(R, d) {
    if (!d || d.seat !== R.rec.me || d.G.v === 'good' || !/^Best play: /.test(String(d.G.head))) return '';
    if (R.whatIf && R.whatIf.at === d.at) {
      const w = R.whatIf.res; if (!w) return '<div class="tr-dim">Couldn’t branch this one.</div>';
      return '<div class="tr-explain tr-narrate"><b>What if: ' + esc(plain(d.G.head.replace(/^Best play: /, 'you had chosen to '))) + '</b><div class="tr-why">' + esc(plain(w.seq.join('\n'))) + (w.board.length ? '\nBoard: ' + esc(cardsTxt(w.board)) : '') + '\n' + esc(plain(w.result)) + '\n<b class="tr-lbl">That line finishes ' + (w.net >= 0 ? '+' : '') + esc(bbs(w.net)) + '</b> against ' + (R.rec.net >= 0 ? '+' : '') + esc(bbs(R.rec.net)) + ' for what you did. One run of the cards — the decision, not the result, is the lesson.</div></div>';
    }
    return '<div class="tr-row"><button class="ghost" data-act="hist:whatif">▶ What if I had ' + esc(plain(d.G.head.replace(/^Best play: /, ''))) + '?</button></div>';
  }
  function renderHands() {
    const m = $('trMain'), R = drill.replay;
    if (!R) {
      m.innerHTML = '<div class="tr-drill"><div class="tr-q"><b>Hand history</b><br><span class="tr-dim">Your last ' + history.length + ' hand' + (history.length === 1 ? '' : 's') + '. Replay any of them one action at a time, with the explanation at each decision.</span></div>'
        + (history.length ? history.map(h => {
          const mine = h.dec.filter(d => d.seat === h.me), matched = mine.filter(d => d.G.v !== 'bad').length;
          return '<div class="tr-histrow"><b>Hand #' + h.handNo + (h.tour ? ' · tournament' : '') + '</b><span>' + esc(plain(h.pos)) + ' · ' + esc(h.cards) + ' — ' + esc(handWords(h.k)) + '</span>'
            + '<span class="' + (h.net > 0 ? 'tr-up' : h.net < 0 ? 'tr-down' : '') + '">' + (h.net > 0 ? '+' : '') + esc(plain(bbs(h.net))) + '</span>'
            + '<span class="tr-dim">' + mine.length + ' decision' + (mine.length === 1 ? '' : 's') + (mine.length ? ', ' + matched + ' matched the best play' : '') + '</span>'
            + '<button class="ghost" data-act="hist:open:' + esc(h.id) + '">▶ Replay</button></div>';
        }).join('') : '<div class="tr-dim">No hands yet — play some on the Play tab and they appear here.</div>') + '</div>';
      return;
    }
    const rec = R.rec, total = rec.acts.length, rg = replayGame(rec, R.step);
    const saved = { g, me, room, show: opts.showBots };
    let felt;
    g = rg; me = rec.me; room = null; opts.showBots = true;
    try { felt = feltHtml(); } finally { g = saved.g; me = saved.me; room = saved.room; opts.showBots = saved.show; }
    const actions = rg.log.filter(l => l.kind !== 'post'), last = R.step > 0 ? actions[R.step - 1] : null;
    const who = i => i === rec.me ? 'You' : rec.seats[i].n;
    const d = rec.dec.find(x => x.at === R.step - 1);
    const what = last ? who(last.i) + ' (' + last.pos + ') ' + last.txt : 'The deal: blinds posted, cards dealt.';
    const end = rg.over && R.step >= total ? '\n' + rg.result.wins.map(w => who(w.i) + ' win' + (w.i === rec.me ? '' : 's') + ' ' + bbs(r2(w.amt)) + (w.name ? ' — ' + w.name : '')).join('\n') : '';
    setPanel('<div class="tr-explain tr-narrate"><b>' + esc(plain(what)) + '</b>' + (end ? '<div class="tr-why">' + esc(plain(end)) + '</div>' : '')
      + (d ? '<div class="tr-why"><b class="tr-lbl">' + esc(plain(who(d.seat) + ' chose: ' + (d.verb || d.kind) + ' · ' + d.G.head)) + '</b>\n' + fmtWhy(d.G.why) + '</div>' + (d.street === 0 ? chartMini(d.G.view, d.G.k) : '') + detailHtml(d.detail, true) + whatIfHtml(R, d) : '') + '</div>');
    m.innerHTML = '<div class="tr-replay-head"><button class="ghost" data-act="hist:close">← All hands</button><b>Replay · hand #' + rec.handNo + '</b><span class="tr-dim">Step ' + R.step + ' of ' + total + ' · every card is shown</span></div>'
      + '<div class="tr-felt-wrap"><div class="tr-felt">' + felt + '</div></div>'
      + '<div class="tr-actions"><button class="ghost" data-act="hist:first"' + (R.step ? '' : ' disabled') + '>⏮ Start</button><button class="ghost" data-act="hist:prev"' + (R.step ? '' : ' disabled') + '>◀ Back</button>'
      + '<button class="primary" data-act="hist:next"' + (R.step < total ? '' : ' disabled') + '>Next ▶</button><button class="ghost" data-act="hist:last"' + (R.step < total ? '' : ' disabled') + '>End ⏭</button></div>';
  }
  function summarize() {
    summarized = handKey();
    if (g.result && g.result.wins.reduce((a, w) => a + w.amt, 0) >= 60) talkEvent('bigpot');
    const mine = decisions.filter(d => d.seat === me), T = g.tour;
    const counts = !autoOn() && !mine.some(d => d.auto);          // a hand the Angel played isn't part of your session
    let head = 'Hand #' + g.handNo + ' over';
    if (me >= 0 && g.players[me] && T) {
      const net = r2(g.players[me].stack - g.startStacks[me]);
      if (counts) {
        stats.hands++;
        if (mine.some(d => d.street === 0 && (d.kind === 'call' || d.kind === 'raise'))) stats.vpip++;
        if (mine.some(d => d.street === 0 && d.kind === 'raise')) stats.pfr++;
        saveStats();
      }
      if (!g.players[me].out) head += ': ' + (net >= 0 ? '+' : '') + bbs(net);
    } else if (me >= 0 && g.players[me]) {
      const net = r2(g.players[me].stack - (g.startStacks ? g.startStacks[me] : 100));
      if (counts) {
        stats.hands++; stats.net = r2(stats.net + net);
        if (mine.some(d => d.street === 0 && (d.kind === 'call' || d.kind === 'raise'))) stats.vpip++;
        if (mine.some(d => d.street === 0 && d.kind === 'raise')) stats.pfr++;
        saveStats();
      }
      head += ': ' + (net >= 0 ? '+' : '') + bbs(net);
    }
    const res = g.result.wins.map(w => (w.i === me ? 'You win ' : g.players[w.i].name + ' wins ') + bbs(r2(w.amt)) + (w.name ? ' — ' + w.name : '')).join('\n');
    // Was it the cards or the decisions? Both numbers are on the hand; this is the one sentence that joins them.
    let verdict = '';
    if (me >= 0 && g.players[me] && mine.length) {
      const net = r2(g.players[me].stack - (g.startStacks ? g.startStacks[me] : 100)), bad = mine.filter(d => d.G.v === 'bad'), cost = r2(bad.reduce((a, d) => a + (d.G.loss || 0), 0));
      const one = bad.length === 1 ? STREET[bad[0].street].toLowerCase() + ' (' + bad[0].G.head.replace(/^Best play: /, 'best was ') + ')' : bad.length + ' decisions';
      if (!bad.length && net <= -3) verdict = 'You matched the best play on every decision and still lost ' + bbs(-net) + ' — that was the cards, not your play.';
      else if (!bad.length && net >= 3) verdict = 'You matched the best play and won ' + bbs(net) + ' — the result and the decisions agree.';
      else if (!bad.length) verdict = 'Every decision matched the best play; the hand was about even.';
      else if (net > 0) verdict = 'You won ' + bbs(net) + ', but ' + (bad.length === 1 ? 'one decision differed from the best play on the ' + one : one + ' differed from the best play') + ' — the result flattered the play.';
      else verdict = 'You lost ' + bbs(-net) + ', and ' + (bad.length === 1 ? 'one decision differed from the best play on the ' + one : one + ' differed from the best play') + (cost > 0 ? ' — those cost about ' + bbs(cost) + ' of it' : '') + '. The rest was the cards.';
    }
    const tl = tableLessonLine();
    const shows = room ? g.players.map((p, j) => p.cards ? (j === me ? 'You' : p.name) + ': ' + cardsTxt(p.cards) + (p.folded ? ' (folded)' : '') : '').filter(Boolean).join('\n') : '';
    const lines = decisions.filter(d => room || d.seat === me).map(d => '• ' + (room ? (d.seat === me ? 'You' : d.name) + ', ' : '') + STREET[d.street] + ': chose ' + (d.verb || d.kind) + ' · ' + d.G.head
      + (d.Eact != null ? ' (' + d.Eact + '% vs the actual cards)' : '')).join('\n');
    feed('', '<b>' + esc(head) + '</b>' + esc(res) + (verdict ? '\n\n<b class="tr-lbl">Cards or decisions?</b> ' + esc(plain(verdict)) : '') + (tl ? '\n<b class="tr-lbl">Table lesson:</b> ' + esc(tl) : '') + (shows ? '\n\n' + esc(shows) : '') + (lines ? '\n\n' + esc(lines) : ''));
    if (T) tourNews();
    if (me >= 0) dailyAdd('hands');
    saveHand();
  }
  // ---- today's challenges (from PokerStars' daily challenges): small goals that build the habit ----
  const DAILY_KEY = 'pokerangel.daily';
  const GOALS = [['hands', 'Play 20 hands', 20], ['pre', 'Answer 10 preflop spots', 10], ['pf', 'Answer 10 push/fold spots', 10], ['icm', 'Answer 5 prize-money spots', 5]];
  function daily() {
    const today = new Date().toISOString().slice(0, 10); let d = null;
    try { d = JSON.parse(ls(DAILY_KEY) || 'null'); } catch (e) { d = null; }
    return d && d.date === today ? d : { date: today };
  }
  function dailyAdd(k) { const d = daily(); d[k] = (d[k] || 0) + 1; ls(DAILY_KEY, JSON.stringify(d)); }
  function dailyHtml() {
    const d = daily(), done = GOALS.filter(([k, , n]) => (d[k] || 0) >= n).length;
    return '<div class="tr-daily"><b>Today’s challenges</b><span class="tr-dim">' + done + ' of ' + GOALS.length + ' done</span>' + GOALS.map(([k, label, n]) => {
      const v = Math.min(d[k] || 0, n);
      return '<div class="tr-goal' + (v >= n ? ' done' : '') + '"><span>' + label + '</span><span class="tr-bar"><i style="width:' + Math.round(v / n * 100) + '%"></i></span><small>' + v + ' / ' + n + '</small></div>';
    }).join('') + '</div>';
  }
  // Knock-outs, blind rises and the final result, from the state the hand left behind.
  function tourNews() {
    const T = g.tour;
    const out = g.players.map((p, i) => i).filter(i => !g.players[i].out && T.chips[i] <= 0);
    for (const i of out) feed(i === me ? 'bad' : '', '<b>' + esc((i === me ? 'You are' : g.players[i].name + ' is') + ' out in ' + ordinal(T.place[i])) + '</b>' + (T.prize[i] ? 'Wins $' + T.prize[i] + '.' : 'No prize.') + (i === me && !T.done ? ' The tournament plays on — watch it out, or start another.' : ''));
    if (T.levelUp && !T.done) feed('', '<b>⬆ Blinds up — level ' + (T.level + 1) + '</b>' + blindsTxt(T) + '. Stacks are now shallower: everyone’s count in big blinds just fell.');
    if (T.done) {
      const order = g.players.map((p, i) => i).sort((a, b) => T.place[a] - T.place[b]);
      const mine = T.place[me];
      if (me >= 0 && mine) {
        stats.tourneys = (stats.tourneys || 0) + 1; stats.tourPrize = (stats.tourPrize || 0) + T.prize[me]; stats.tourCost = (stats.tourCost || 0) + T.pool / g.players.length;
        if (T.prize[me] > 0) stats.itm = (stats.itm || 0) + 1;
        if (mine === 1) stats.wins = (stats.wins || 0) + 1;
        saveStats();
      }
      feed(mine === 1 ? 'good' : '', '<b>🏆 Tournament over' + (me >= 0 && mine ? ' — you finished ' + ordinal(mine) + (T.prize[me] ? ' for $' + T.prize[me] : '') : '') + '</b>'
        + esc(order.map(i => ordinal(T.place[i]) + '  ' + (i === me ? 'You' : g.players[i].name) + (T.prize[i] ? '  $' + T.prize[i] : '')).join('\n')));
    }
  }
  // Fast-fold (from PokerStars' Zoom): solo cash games only. Once you fold, you're dealt straight into
  // the next hand — after you've read the explanation, if "Explain after I act" is on.
  const fastFolding = () => !room && !autoOn() && g && !g.tour && opts.fastFold && g.players[me] && g.players[me].folded;
  function handEnd() {
    g._done = true;
    onHandState();
    if (tab === 'play') renderPlay();
    if (fastFolding() && !(pauseOn() && myPending())) {
      const tok = ++token;
      setTimeout(() => { if (tok === token && g && g.over && shown && tab === 'play') startHand(); }, 250);
    }
    // Nothing deals by itself: the next hand waits for Next hand. The one exception is a solo
    // tournament you're already out of, which plays itself out so you can see who wins.
    if (g.tour && !g.tour.done && !room && g.players[me] && g.players[me].out && g.players[me].out !== 'watching') {
      const tok = ++token;
      setTimeout(() => { if (tok === token && g && g.over) startHand(); }, 500);
    }
  }
  async function askAI(btn) {
    if (!g || !g.over) return;
    if (btn) btn.disabled = true;
    const ph = feed('', '<b>🤖 AI coach</b>Thinking…');
    if (ph) ph.classList.add('open');
    const head = '<b>🤖 AI coach — hand #' + g.handNo + '</b>';
    try {
      let text;
      if (window.api && window.api.draft) text = await window.api.draft({ system: AI_COACH, user: levelAiLine() + '\n\n' + historyText(g, decisions) });
      else {
        // claude.ai: ask Claude on the viewer's own account (they're asked once to allow it)
        const sample = window.claude && await window.claude.use('sample');
        if (!sample) throw { code: 'not_granted' };
        text = (await sample(AI_COACH + '\n\n' + levelAiLine() + '\n\n' + historyText(g, decisions), { onText: ({ text: t }) => { if (ph) ph.innerHTML = head + esc(t); } })).text;
      }
      if (ph) ph.innerHTML = head + esc(text || '(no answer)');
    } catch (e) {
      const why = e && e.code === 'not_granted' ? 'Claude isn’t allowed on this page for you, so the hand review is off. The grades above still work.'
        : e && e.code === 'rate_limited' ? 'You’ve asked Claude a lot just now. Try again in a little while.' : cleanErr(e && (e.message || e.code) || e);
      if (ph) { ph.className = 'tr-msg bad'; ph.innerHTML = '<b>AI coach unavailable</b>' + esc(why); }
    } finally { if (btn) btn.disabled = false; }
  }

  // ---- the friends' table: hosting ----
  function newCode() { const A = 'ABCDEFGHJKMNPQRSTUVWXYZ23456789'; let s = ''; for (let k = 0; k < 5; k++) s += A[Math.floor(Math.random() * A.length)]; return s; }
  function noPeer() { if (typeof Peer === 'function') return false; toast('The connection library didn’t load — playing with friends is unavailable', 'red'); return true; }
  function hostTable() {
    if (WEB) return hostTableWeb();
    if (noPeer() || room) return;
    const code = newCode();
    const peer = new Peer(PEER_PREFIX + code.toLowerCase(), PEER_OPTS);
    autoStop(true); room = { role: 'host', code, peer, conns: new Map(), faceUp: !!opts.faceUp, pw: String(($('trPw') || {}).value || '').trim().slice(0, 24), status: 'Opening the table…', voices: {} }; ratings = {};
    if (HAS_TTS() && opts.myVoiceName && libVoiceId(opts.myVoiceName)) room.voices[myName()] = libVoiceId(opts.myVoiceName);
    me = 0; g = null; decisions = []; token++; renderPlay();       // any solo hand in progress is abandoned
    peer.on('open', () => { if (room && room.peer === peer) { room.status = ''; renderPlay(); feed('', '<b>👥 Table ' + code + ' is open</b>Send your friends the code. They open Poker Angel → 🎓 Trainer → Join, and type it in.'); } });
    peer.on('connection', (conn) => {
      conn.on('data', (m) => onGuestMsg(conn, m));
      conn.on('close', () => guestLeft(conn));
      conn.on('error', () => guestLeft(conn));
    });
    peer.on('error', (e) => {
      if (!room || room.peer !== peer) return;
      if (e && e.type === 'unavailable-id') { leaveRoom(true); hostTable(); return; }   // code clash: pick another
      if (e && /network|server-error|socket/.test(e.type || '')) { room.status = 'Connection to the meeting service lost — retrying…'; renderPlay(); try { peer.reconnect(); } catch (x) {} return; }
      toast('Table: ' + (e && (e.message || e.type) || 'error'), 'red');
    });
  }
  const reserved = j => Array.from(room.conns.values()).some(c => c.seat === j);
  function onGuestMsg(conn, m) {
    if (!isHost() || !m || typeof m !== 'object') return;
    if (m.t === 'hello') {
      if (room.conns.has(conn)) return;
      if (room.pw && String(m.pw || '') !== room.pw) { try { conn.send({ t: 'wrongpw' }); } catch (e) {} setTimeout(() => { try { conn.close(); } catch (e) {} }, 800); return; }
      const name = String(m.name || 'Friend').replace(/[^\w .'-]/g, '').trim().slice(0, 16) || 'Friend';
      let seat = -1;
      for (let j = 1; j < (g ? g.players.length : NSEATS) && seat < 0; j++) if (!reserved(j) && (!g || !isHuman(g.players[j]))) seat = j;
      if (seat < 0) { try { conn.send({ t: 'full' }); } catch (e) {} setTimeout(() => { try { conn.close(); } catch (e) {} }, 800); return; }
      room.conns.set(conn, { seat, name, pending: true, talk: m.talk !== false });
      feed('', '<b>👋 ' + esc(name) + ' joined</b>' + (g ? 'Dealt in from the next hand.' : 'Deal when everyone’s here.'));
      talkEvent('greet', { name });
      broadcast(); if (tab === 'play') renderPlay();
    } else if (m.t === 'act') {
      const c = room.conns.get(conn);
      if (c && !c.pending && g && g.handNo === m.handNo && g.toAct === c.seat) doAct(c.seat, String(m.type || ''), Number(m.to));
    } else if (m.t === 'voice') {
      const c = room.conns.get(conn); if (!c || typeof m.b64 !== 'string' || m.b64.length > 12e6) return;
      if (!HAS_TTS()) { if (!room.voiceNote) { room.voiceNote = true; feed('', '<b>🎙 ' + esc(c.name) + ' sent a table voice</b>To hear your friends’ voices at the table, set up ElevenLabs in ⚙ Settings → Voice and tick 🗣 Table chatter.'); } return; }
      window.api.ttsClone({ name: c.name, mime: String(m.mime || ''), b64: m.b64, hash: String(m.hash || '') })
        .then(r => { if (room && room.voices) { room.voices[c.name] = r.voiceId; toast('🎙 ' + c.name + '’s voice is ready' + (r.reused ? ' (from last time)' : ''), 'green'); } })
        .catch(e => toast(c.name + '’s voice: ' + cleanErr(e), 'red'));
    }
  }
  // Friends who joined since the last deal take their seats (replacing that seat's bot).
  function seatJoiners() {
    if (g.tour && g.handNo > 0) return;                          // mid-tournament: joiners wait for the next game
    for (const c of room.conns.values()) if (c.pending) { g.players[c.seat] = { name: c.name, style: null }; c.pending = false; }
    // A bot never shares a name with a person at the table ("Mia" the friend vs Mia the bot).
    const taken = new Set(g.players.filter(isHuman).map(p => p.name.toLowerCase()));
    g.players.forEach(p => {
      if (isHuman(p) || !taken.has(p.name.toLowerCase())) return;
      const free = BOTS.find(n => !g.players.some(q => q.name.toLowerCase() === n.toLowerCase()) && !taken.has(n.toLowerCase()));
      p.name = free || p.name + ' (bot)';
    });
  }
  function guestLeft(conn) {
    if (!isHost() || !room.conns.has(conn)) return;
    const c = room.conns.get(conn); room.conns.delete(conn);
    feed('', '<b>' + esc(c.name) + ' left the table</b>' + (c.pending ? '' : 'A bot plays their seat.'));
    if (!c.pending && g) {
      const p = g.players[c.seat]; p.style = 'tag'; p.name = c.name + ' (bot)';
      if (!g.over && g.toAct === c.seat) step();
    }
    broadcast(); if (tab === 'play') renderPlay();
  }
  function tablePlayers() {
    const out = [{ name: myName() + ' (host)', seat: 0 }];
    if (room && room.conns) for (const c of room.conns.values()) out.push({ name: c.name + (c.pending && g ? ' (next hand)' : ''), seat: c.seat });
    return out;
  }
  // The table as one seat may see it: no deck, and other players' cards hidden unless the table is
  // face up or the hand is over.
  function publicState(seat) {
    if (!g) return null;
    const reveal = room.faceUp || g.over;
    const players = g.players.map((p, j) => Object.assign({}, p, { cards: (reveal || j === seat) ? p.cards : null, post: (p.post || []).slice() }));
    return Object.assign({}, g, { players, deck: [] });
  }
  function broadcast() {
    if (!isHost()) return;
    if (room.web) { if (room.r) broadcastWeb(); return; }
    const players = tablePlayers();
    for (const [conn, c] of room.conns) {
      if (!conn.open) continue;
      const seat = c.pending ? -1 : c.seat;
      try { conn.send({ t: 'state', g: publicState(seat), decisions: g ? visibleDecisions(seat) : [], seat, faceUp: room.faceUp, code: room.code, players }); } catch (e) {}
    }
  }

  // ---- the friends' table: joining ----
  function joinTable(code) {
    if (WEB) return joinTableWeb(code);
    if (noPeer() || room) return;
    code = String(code || '').toUpperCase().replace(/[^A-Z0-9]/g, '');
    if (code.length !== 5) { toast('A table code is 5 letters/numbers', 'red'); return; }
    const peer = new Peer(PEER_OPTS);
    autoStop(true); room = { role: 'guest', code, peer, conn: null, faceUp: true, players: [], status: 'Connecting to table ' + code + '…' }; ratings = {};
    g = null; me = -1; decisions = []; renderPlay();
    const giveUp = setTimeout(() => { if (room && room.peer === peer && !(room.conn && room.conn.open)) { toast('Couldn’t reach table ' + code + ' — check the code and that the host is still there', 'red'); leaveRoom(true); } }, 20000);
    peer.on('open', () => {
      const conn = peer.connect(PEER_PREFIX + code.toLowerCase(), { reliable: true, serialization: 'json' });
      room.conn = conn;
      conn.on('open', () => { clearTimeout(giveUp); room.status = ''; conn.send({ t: 'hello', name: myName(), talk: opts.myTalk !== false, pw: String(($('trPw') || {}).value || '').trim().slice(0, 24) }); voicePayload().then(vp => { if (vp && conn.open) { try { conn.send(vp); } catch (e) {} } }); feed('', '<b>👥 Joined table ' + code + '</b>You’re dealt in from the next hand.'); renderPlay(); });
      conn.on('data', onHostMsg);
      conn.on('close', () => { if (room && room.conn === conn) { toast('The host closed the table', 'red'); leaveRoom(true); } });
    });
    peer.on('error', (e) => {
      if (!room || room.peer !== peer) return;
      clearTimeout(giveUp);
      toast(e && e.type === 'peer-unavailable' ? 'No table with the code ' + code + ' is open' : 'Couldn’t connect: ' + (e && (e.message || e.type)), 'red');
      leaveRoom(true);
    });
  }
  function onHostMsg(m) {
    if (!isGuest() || !m || typeof m !== 'object') return;
    if (m.t === 'full') { toast('That table is full (' + NSEATS + ' players)', 'red'); leaveRoom(true); return; }
    if (m.t === 'wrongpw') { toast('That table has a password — type it next to the code', 'red'); leaveRoom(true); return; }
    if (m.t === 'say') return onSay(m);
    if (m.t !== 'state') return;
    Object.assign(room, { faceUp: !!m.faceUp, players: m.players || [] });
    me = typeof m.seat === 'number' ? m.seat : -1;
    const fresh = g && m.g && m.g.handNo !== g.handNo;
    g = m.g || null; decisions = m.decisions || [];
    if (g) onHandState();
    if (tab === 'play' && shown) renderPlay(); else renderSpot();
    if (fresh) showTable();
  }
  function leaveRoom(quiet) {
    if (!room) return;
    const r = room; room = null;
    try { if (r.web) { if (r.off) r.off(); if (r.r) r.r.leave(); } else r.peer.destroy(); } catch (e) {}
    token++;
    if (r.role === 'guest') { g = null; me = 0; decisions = []; }
    else if (g) g.players.forEach((p, j) => { if (j !== 0 && isHuman(p)) { p.style = 'tag'; p.name += ' (bot)'; } });
    me = 0;
    if (!quiet) toast('You left the table', '');
    if (tab === 'play') renderPlay();
  }

  // ---- the friends' table on claude.ai: the `room` capability ------------------------------------
  // A web page there can't open direct connections, and room messages are capped at 4 KB — less
  // than a whole table. So the host publishes, in its own presence, only a REPLAY RECORD: who sits
  // where, the table just before the deal, the shuffle's seed and the hand's actions so far. Every
  // guest rebuilds the hand from it with this same engine (the same seed deals the same cards) and
  // grades the people's decisions itself. A guest sends a move by putting it in its own presence —
  // presence is open to every viewer, so friends need no more than view access. Bots, timing and
  // validation stay on the host. Each table is a named room, so tables don't hear each other.
  // (Everyone's page holds the whole hand here: "own cards only" is a display setting among
  // friends, not a lock.)
  const WEB = typeof window !== 'undefined' && !!(window.claude && typeof window.claude.use === 'function') && !(window.api && window.api.draft);
  // In a web page (claude.ai or a public site) rather than the desktop app: friends open the same page.
  const IN_BROWSER = typeof window !== 'undefined' && !(window.api && window.api.draft);
  // The AI hand review needs the desktop app's key or a claude.ai page; a public page has neither.
  const HAS_AI = typeof window !== 'undefined' && !!((window.api && window.api.draft) || (window.claude && window.claude.use));
  let _room = null;
  const roomCap = async () => _room || (_room = await window.claude.use('room'));
  const roomName = code => 'pa-' + code.toLowerCase();
  const myPeer = () => { const p = room && room.r && room.r.peers().find(x => x.sameTab); return p ? p.peer : null; };
  async function hostTableWeb() {
    if (room) return;
    const R = await roomCap().catch(() => null);
    if (!R) { toast('Playing with friends works when this page is open on claude.ai and you’re signed in', 'red'); return; }
    const code = newCode();
    autoStop(true); room = { role: 'host', web: true, code, conns: new Map(), faceUp: true, status: 'Opening the table…' }; ratings = {};
    me = 0; g = null; decisions = []; token++; renderPlay();
    try { room.r = await R.join(roomName(code)); } catch (e) { room = null; toast('Couldn’t open a table (' + (e && e.code || 'error') + ')', 'red'); renderPlay(); return; }
    room.status = '';
    room.off = room.r.onPeers(onPeersHost);
    broadcast(); renderPlay();
    feed('', '<b>👥 Table ' + code + ' is open</b>Send your friends this page’s link and the code. They open 🎓 Trainer → Join, and type it in.');
  }
  function onPeersHost(change) {
    if (!isHost() || !room.web) return;
    for (const p of change.peers) {
      if (p.sameTab) continue;
      const pr = p.presence || {};
      if (pr.join && !room.conns.has(p.peer)) {
        const name = String(pr.join).replace(/[^\w .'-]/g, '').trim().slice(0, 16) || 'Friend';
        let seat = -1;
        for (let j = 1; j < (g ? g.players.length : NSEATS) && seat < 0; j++) if (!reserved(j) && (!g || !isHuman(g.players[j]))) seat = j;
        if (seat < 0) continue;                                   // full: they see no seat and the page says so
        room.conns.set(p.peer, { seat, name, pending: true });
        feed('', '<b>👋 ' + esc(name) + ' joined</b>' + (g ? 'Dealt in from the next hand.' : 'Deal when everyone’s here.'));
        broadcast(); if (tab === 'play') renderPlay();
      }
      const a = pr.act, c = room.conns.get(p.peer);
      if (a && c && !c.pending && g && !g.over && a.k === handKey() && a.n === g.acts.length && g.toAct === c.seat) doAct(c.seat, String(a.type || ''), Number(a.to));
    }
    for (const p of change.left) if (room.conns.has(p.peer)) guestLeft(p.peer);
  }
  function broadcastWeb() {
    const seats = g ? g.players.map((p, i) => {
      let peer = null; for (const [k, c] of room.conns) if (c.seat === i && !c.pending) peer = k;
      return { n: p.name, s: p.style || null, l: p.level || null, peer };
    }) : null;
    const lobby = tablePlayers().map(p => p.name);
    const pending = Array.from(room.conns.entries()).filter(([, c]) => c.pending).map(([k]) => k);
    const rec = { v: 1, code: room.code, faceUp: room.faceUp, lobby, pending, seats,
      g: g ? { gid: g.gid, handNo: g.handNo, seed: g.seed, start: g.start, acts: g.acts || [] } : null };
    room.r.presence({ pa: rec }).catch(e => { if (e && e.code === 'invalid_argument') console.error('table record too large', e.message); });
  }
  async function joinTableWeb(code) {
    if (room) return;
    code = String(code || '').toUpperCase().replace(/[^A-Z0-9]/g, '');
    if (code.length !== 5) { toast('A table code is 5 letters or numbers', 'red'); return; }
    const R = await roomCap().catch(() => null);
    if (!R) { toast('Playing with friends works when this page is open on claude.ai and you’re signed in', 'red'); return; }
    autoStop(true); room = { role: 'guest', web: true, code, faceUp: true, players: [], status: 'Looking for table ' + code + '…' }; ratings = {};
    g = null; me = -1; decisions = []; renderPlay();
    try { room.r = await R.join(roomName(code)); } catch (e) { room = null; toast('Couldn’t join (' + (e && e.code || 'error') + ')', 'red'); renderPlay(); return; }
    const mine = room;
    room.r.presence({ join: myName() }).catch(() => {});
    room.off = room.r.onPeers(onPeersGuest);
    setTimeout(() => { if (room === mine && !room.hostPeer) { toast('No table with the code ' + code + ' is open — check the code with the host', 'red'); leaveRoom(true); } }, 15000);
  }
  function onPeersGuest(change) {
    if (!isGuest() || !room.web) return;
    const host = change.peers.find(p => !p.sameTab && p.presence && p.presence.pa && p.presence.pa.code === room.code);
    if (!host) {
      if (room.hostPeer && !change.peers.some(p => p.peer === room.hostPeer)) { toast('The host closed the table', 'red'); leaveRoom(true); }
      return;
    }
    if (!room.hostPeer) { room.hostPeer = host.peer; feed('', '<b>👥 Joined table ' + esc(room.code) + '</b>You’re dealt in from the next hand.'); }
    if (host.presence === room.lastPres) return;
    room.lastPres = host.presence;
    try { applyRecord(host.presence.pa); } catch (e) { console.error('table replay', e); }
  }
  // Rebuild the host's table from its record. Only new actions are played (and graded) on top of
  // what this page already has; a new hand, or anything that doesn't line up, starts the hand afresh.
  function applyRecord(rec) {
    room.status = '';
    room.faceUp = !!rec.faceUp; room.players = (rec.lobby || []).map(n => ({ name: String(n) }));
    const mp = myPeer();
    const seat = rec.seats ? rec.seats.findIndex(s => s && s.peer === mp) : -1;
    if (!rec.g || !rec.seats) { g = null; decisions = []; me = seat; if (tab === 'play' && shown) renderPlay(); else renderSpot(); return; }
    const R = rec.g, acts = Array.isArray(R.acts) ? R.acts : [];
    const fresh = !g || g.gid !== R.gid || g.handNo !== R.handNo || g.seed !== R.seed || (g.acts || []).length > acts.length;
    if (fresh) {
      g = { players: rec.seats.map(s => ({ name: String(s.n || 'Seat'), style: s.s && STYLES[s.s] ? s.s : null, level: s.l && SKILL[s.l] ? s.l : null })), button: R.start.button, handNo: R.start.handNo, gid: R.gid };
      if (R.start.tour) g.tour = JSON.parse(JSON.stringify(R.start.tour));
      g.lastBB = R.start.lastBB; g.prevAlive = R.start.prevAlive;
      g.start = R.start; g.seed = R.seed;
      newHand(g, mulberry(R.seed)); decisions = [];
    }
    me = seat;
    rec.seats.forEach((s, i) => { const p = g.players[i]; if (p && s) { p.name = String(s.n || p.name); p.style = s.s && STYLES[s.s] ? s.s : null; p.level = s.l && SKILL[s.l] ? s.l : null; } });
    for (let k = g.acts.length; k < acts.length; k++) {
      const [i, kind, to] = acts[k];
      if (g.over || g.toAct !== i) { console.error('table replay out of step at action ' + k); break; }
      if (isHuman(g.players[i])) gradeAndAct(i, kind, to); else act(g, i, { type: kind, to });
    }
    if (room.sent && room.sent !== handKey() + '/' + g.acts.length) room.sent = null;
    onHandState();
    if (tab === 'play' && shown) renderPlay(); else renderSpot();
  }

  // ---- drawing the table ----
  function sizes() {
    const L = legal(g, me), pos = posOf(g, me), out = [];
    const add = (to, label) => { to = half(to); if (to >= L.minTo && to < L.maxTo && !out.some(o => o.to === to)) out.push({ to, label: label + ' ' + bbs(to) }); };
    if (g.street === 0) {
      if (g.raises === 0) { add(openTo(g, me), 'Raise to'); add(openTo(g, me) + 1, 'Raise to'); }
      else if (g.raises === 1) add(threeBetTo(g, me), '3-bet to');
      else if (g.raises === 2) add(g.curBet * 2.3, '4-bet to');
    } else if (g.curBet === 0) {
      [[0.33, '⅓ pot'], [0.5, '½ pot'], [0.75, '¾ pot'], [1, 'Pot']].forEach(([f, n]) => add(Math.max(1, L.pot * f), n + ' ·'));
    } else [2.5, 3.5].forEach(m => add(g.curBet * m, 'Raise ' + m + '× to'));
    out.push({ to: L.maxTo, label: 'All-in ' + bbs(L.maxTo) });
    void pos;
    return out;
  }
  // The comment on the move just made sits in a box beside that player until the next move. With their
  // cards face up (you folded, or "Show the bots' cards") it's the bot's own reason; otherwise only
  // what the table can see — what that action says about their hand.
  function seatNote(i) {
    if (i === me && me >= 0) {                                    // you: just above your cards
      const p = g.players[me]; if (g.over || !p || !p.cards || !p.cards.length) return '';
      const [x, y] = layout().seat[view(me)], box = (cls, head, body) => '<div class="tr-note hero ' + cls + '" style="left:' + x + '%;top:' + y + '%"><b>' + esc(plain(head)) + '</b>' + esc(plain(body)) + '</div>';
      const d = decisions.filter(q => q.seat === me).pop();
      if (d && d.at === g.acts.length - 1) {                      // the move you just made: its grade and the gist
        const ls = String(d.G.why || '').split('\n').filter(Boolean), gist = ls.find(l => /^So:/.test(l)) || ls[0] || '';
        return box(d.G.v, (autoOn() ? 'The Angel: ' : 'You ') + (d.verb || d.kind) + ' · ' + d.G.head, gist.replace(/^So:\s*/, '').replace(/^./, c => c.toUpperCase()));
      }
      if (g.toAct !== me || p.folded) return '';
      // your turn: what you hold and what it costs — not the answer (that's 💡 Hint / "Advise me")
      const k = cls(p.cards[0], p.cards[1]), L = legal(g, me);
      let head, line = '';
      if (!g.board.length) { head = handWords(k); line = strengthWord(pct()[k]).replace(/^./, c => c.toUpperCase()) + ' — #' + (PK_HAND_ORDER.indexOf(k) + 1) + ' of 169 starting hands.\n'; }
      else {
        const dr = draws(p.cards, g.board), bits = [handName(evalHand(p.cards.concat(g.board)))];
        if (dr.flush) bits.push('flush draw'); if (dr.straight) bits.push('straight draw');
        head = bits.join(' + ');
      }
      line += L.toCall > 0 ? 'Call ' + bbs(L.toCall) + ' into ' + bbs(L.pot) + ': you need to win ' + Math.round(L.toCall / (L.pot + L.toCall) * 100) + '% of the time.' : 'No bet to you — checking is free.';
      return '<div class="tr-note hero turn" style="left:' + x + '%;top:' + y + '%"><b>Your turn: ' + esc(head) + '</b>' + esc(line) + '</div>';
    }
    const log = g.watchLog || [], w = log[log.length - 1];
    if (g.over || !w || w.i !== i || w.at !== g.acts.length - 1 || i === me) return '';
    const p = g.players[i], open = opts.showBots || watchOn() || autoOn();
    const read = p.folded ? 'Out of this hand.' : p.rangeW >= 0.99 ? 'Could still have any two cards.' : 'Likely holds one of the best ' + r1(p.rangeW * 100) + '% of hands.';
    const body = open && w.why ? w.why : read + (STYLE_HOW[p.style] ? '\n' + styleName(p.style) + ': ' + STYLE_HOW[p.style] : '');
    const [x, y] = layout().seat[view(i)], side = x < 0 || x > 100 ? (x < 50 ? 'r' : 'l')                     // side seats: in over the felt's edge
      : x >= 35 && x <= 65 ? (y < 50 ? 'b' : 't') : (x < 50 ? 'l' : 'r');                 // corners: outwards, clear of the board
    return '<div class="tr-note ' + side + '" style="left:' + x + '%;top:' + y + '%"><b>' + esc(plain(p.name + ' ' + w.txt)) + '</b>' + esc(plain(body)) + '</div>';
  }
  function seatHtml(i) {
    const p = g.players[i], v = view(i), [x, y] = layout().seat[v], turn = !g.over && g.toAct === i, mine = i === me, T = g.tour;
    if (p.out) {
      return '<div class="tr-seat out" style="left:' + x + '%;top:' + y + '%"><div class="tr-cards"></div><div class="tr-plate"><b>' + esc(mine && room ? 'You' : p.name) + '</b>'
        + '<span class="stk">Out — ' + ordinal(T.place[i]) + (T.prize[i] ? ' · $' + T.prize[i] : '') + '</span></div></div>';
    }
    const won = g.over && g.result && g.result.wins.find(w => w.i === i);
    const show = mine || (room ? (room.faceUp || g.over) : (autoOn() || opts.showBots || watchOn() || (g.over && g.result.showdown && !p.folded)));
    const folded = p.folded && !(room && g.over);
    const cards = folded || !p.cards ? (p.folded ? '' : backHtml(mine ? 'lg' : '') + backHtml(mine ? 'lg' : ''))
      : p.cards.map(c => show ? cardHtml(c, mine ? 'lg' : '') : backHtml(mine ? 'lg' : '')).join('');
    let bubble = '';
    if (won) bubble = '<span class="tr-bubble win">wins ' + bbs(r2(won.amt)) + (won.name ? ' · ' + esc(won.name) : '') + '</span>';
    else { const last = g.log.filter(l => l.i === i && l.kind !== 'post' && (l.st === g.street || g.over)).pop(); if (last) bubble = '<span class="tr-bubble">' + esc(last.txt) + '</span>'; }
    const tag = isHuman(p) ? (room ? '<small class="tr-human">player</small>' : '') : '<small>' + esc(botLabel(p)) + '</small>';
    // once a hand is over the chips are settled (and the level may already have risen), so read them direct
    const chips = T ? '<small class="tr-chips">' + Math.round(g.over ? T.chips[i] : p.stack * T.levels[T.level]).toLocaleString() + ' chips</small>' : '';
    return '<div class="tr-seat' + (turn ? ' turn' : '') + (p.folded ? ' folded' : '') + (won ? ' win' : '') + (mine ? ' hero' : '') + '" style="left:' + x + '%;top:' + y + '%">'
      + '<div class="tr-cards">' + cards + '</div>'
      + '<div class="tr-plate"><b>' + esc(mine && room ? 'You' : p.name) + '</b><span class="pos">' + posOf(g, i) + '</span><span class="stk">' + bbs(r2(p.stack)) + (p.allin && !g.over ? ' · all-in' : '') + '</span>'
      + chips + tag + '</div>' + bubble + '</div>';
  }
  // ---- reading explanations aloud ----
  // The computer's own voice (speechSynthesis): nothing leaves the machine. With "Read explanations
  // aloud" on, each new explanation is read once; 🔊 Read this reads the column on demand.
  const CAN_SPEAK = typeof speechSynthesis !== 'undefined' && typeof SpeechSynthesisUtterance !== 'undefined';
  const RANK_SAY = { A: 'Ace', K: 'King', Q: 'Queen', J: 'Jack', T: 'Ten', 10: 'Ten', 9: 'Nine', 8: 'Eight', 7: 'Seven', 6: 'Six', 5: 'Five', 4: 'Four', 3: 'Three', 2: 'Two' };
  const SUIT_SAY = { '♠': 'spades', '♥': 'hearts', '♦': 'diamonds', '♣': 'clubs' };
  // Text as it should sound: cards in words, no symbols, and the short codes in brackets left out
  // (the full words are always just before them).
  function forSpeech(t) {
    return String(t || '')
      .replace(/(10|[2-9TJQKA])([♠♥♦♣])/g, (m, r, su) => RANK_SAY[r] + ' of ' + SUIT_SAY[su])
      .replace(/\s*\((?:UTG\+1|UTG|LJ|HJ|CO|BTN|SB|BB)\)/g, '')
      .replace(/\s*\((?:[AKQJT2-9]{2}[so]?\+?(?:-[AKQJT2-9]{2}[so]?)?)\)/g, '')
      .replace(/#(\d+)/g, 'number $1').replace(/(\d)\s*×/g, '$1 times')
      .replace(/(\d)bb\b/g, '$1 big blinds')
      .replace(/[\u{1F300}-\u{1FAFF}\u2600-\u27BF\uFE0F]/gu, '')
      .replace(/[→·•]/g, ', ').replace(/\s—\s/g, ', ')
      .replace(/(of (?:spades|hearts|diamonds|clubs)) (?=(?:Ace|King|Queen|Jack|Ten|Nine|Eight|Seven|Six|Five|Four|Three|Two) of )/g, '$1, ')
      .replace(/\s+/g, ' ').replace(/\s+([,.;:])/g, '$1').replace(/([,.;:])(?:\s*[,.;:])+/g, '$1').trim();
  }
  let spokenLast = '', speakTimer = 0;
  // ---- which voice ----
  // Two engines. This PC's own voices (speechSynthesis — free, nothing leaves the machine, but on most
  // Windows PCs only a few dated voices are installed; pick the least robotic, or any the player chose).
  // Or ElevenLabs through main.js (desktop app only): natural voices, or one the family recorded
  // themselves. The Angel's pacing asks voiceBusy(), whichever engine is talking.
  let voiceCfg = { engine: 'local', hasTtsKey: false, ttsVoice: '', ttsVoiceName: '' };
  async function loadVoiceCfg() {
    if (!window.api || !window.api.getConfig) return;
    try { const c = await window.api.getConfig(); voiceCfg = { engine: c.ttsEngine || 'local', hasTtsKey: !!c.hasTtsKey, ttsVoice: c.ttsVoice || '', ttsVoiceName: c.ttsVoiceName || '' }; } catch (e) {}
  }
  const HAS_TTS = () => !!(window.api && window.api.ttsSpeak) && ((voiceCfg.engine === 'eleven' && voiceCfg.hasTtsKey) || voiceCfg.engine === 'own') && !!voiceCfg.ttsVoice;
  const CAN_TALK = () => CAN_SPEAK || HAS_TTS() || pcVoiceOn();
  const localVoices = () => { try { return CAN_SPEAK ? speechSynthesis.getVoices() : []; } catch (e) { return []; } };
  function pickVoice() {
    const vs = localVoices();
    const chosen = opts.voice && vs.find(v => v.name === opts.voice);
    return chosen || vs.find(v => /en-GB/i.test(v.lang) && /natural|online|neural/i.test(v.name))
      || vs.find(v => /^en/i.test(v.lang) && /natural|online|neural/i.test(v.name))
      || vs.find(v => /en-GB/i.test(v.lang) && /Google UK English Female|Sonia|Libby|Hazel|Susan|Maisie/i.test(v.name))   // the gentler of the stock voices
      || vs.find(v => /en-GB/i.test(v.lang) && !/George/i.test(v.name)) || vs.find(v => /en-GB/i.test(v.lang))
      || vs.find(v => /^en/i.test(v.lang) && /Google|Zira|Jenny|Aria|Samantha/i.test(v.name)) || vs.find(v => /^en/i.test(v.lang)) || null;
  }
  const voiceLabel = () => HAS_TTS() ? '🎙 ' + (voiceCfg.ttsVoiceName || 'ElevenLabs voice') : (pickVoice() ? pickVoice().name.replace(/^Microsoft /, '').replace(/ - English.*$/, '') : 'this PC’s voice');
  // sentences merged into passages: ~220 characters for the PC voice (a long utterance can stop part-way in
  // Chromium), ~500 for ElevenLabs (fewer requests, better flow)
  function passages(t, max) {
    const parts = [];
    for (const sentence of t.split(/(?<=[.!?:])\s+/)) {
      if (parts.length && parts[parts.length - 1].length + sentence.length < max) parts[parts.length - 1] += ' ' + sentence; else parts.push(sentence);
    }
    return parts;
  }
  function speakLocal(parts) {
    if (!CAN_SPEAK) return;
    try {
      speechSynthesis.cancel();
      const v = pickVoice(), calm = autoOn() && auto.calm;        // 🌙 sleep story: unhurried, lower, softer
      for (const part of parts) {
        const u = new SpeechSynthesisUtterance(part);
        if (v) { u.voice = v; u.lang = v.lang; } else u.lang = 'en-GB';
        u.rate = calm ? 0.82 : (opts.speakRate || 1); u.pitch = calm ? 0.88 : 1; u.volume = calm ? 0.8 : 1;
        speechSynthesis.speak(u);
      }
      if (speechSynthesis.paused) speechSynthesis.resume();
    } catch (e) { console.error('speech', e); }
  }
  let ttsAudio = null, ttsBusy = false, ttsGen = 0, ttsFails = 0;
  // Phones only play sound that a tap started. The first tap anywhere plays a split second of silence
  // through this one player, which unlocks it; every clip after that goes through the same player.
  let voiceEl = null, voiceUnlocked = false;
  const SILENT_WAV = 'data:audio/wav;base64,UklGRiQAAABXQVZFZm10IBAAAAABAAEAIlYAAESsAAACABAAZGF0YQAAAAA=';
  function unlockVoice() {
    if (voiceUnlocked) return;
    try {
      if (!voiceEl) { voiceEl = new Audio(); voiceEl.setAttribute('playsinline', ''); voiceEl.preload = 'auto'; }
      voiceEl.src = SILENT_WAV; const p = voiceEl.play(); if (p && p.then) p.then(() => { voiceUnlocked = true; }, () => {}); else voiceUnlocked = true;
      if (CAN_SPEAK) { try { const u = new SpeechSynthesisUtterance(' '); u.volume = 0; speechSynthesis.speak(u); } catch (e) {} }   // and the phone's own voice
    } catch (e) {}
  }
  // Play one clip to the end through the shared player (falls back to a fresh element on the desktop).
  function playVoiceClip(mime, b64) {
    return new Promise(res => {
      const url = blobUrl(mime, b64), done = () => { URL.revokeObjectURL(url); res(); };
      const a = voiceEl || new Audio(); if (!voiceEl) voiceEl = a;
      a.onended = done; a.onerror = e => { console.error('voice clip', e); done(); };
      a.src = url; const p = a.play(); if (p && p.catch) p.catch(e => { console.error('voice play', e); done(); });
    });
  }
  const blobUrl = (mime, b64) => { const bin = atob(b64), u8 = new Uint8Array(bin.length); for (let i = 0; i < bin.length; i++) u8[i] = bin.charCodeAt(i); return URL.createObjectURL(new Blob([u8], { type: mime })); };
  function ttsStop() { ttsGen++; ttsBusy = false; if (ttsAudio) { try { ttsAudio.pause(); } catch (e) {} ttsAudio = null; } }
  const voiceClipPlaying = () => !!(voiceEl && !voiceEl.paused && !voiceEl.ended && voiceEl.src && voiceEl.src !== SILENT_WAV);
  async function ttsSay(parts) {
    const gen = ++ttsGen; ttsBusy = true;
    const calm = autoOn() && auto.calm, speed = calm ? 0.85 : (opts.speakRate || 1);
    let k = 0;
    try {
      let next = window.api.ttsSpeak({ text: parts[0], speed, calm });              // the next passage is fetched while this one plays
      for (k = 0; k < parts.length; k++) {
        const r = await next; if (gen !== ttsGen) return;
        next = k + 1 < parts.length ? window.api.ttsSpeak({ text: parts[k + 1], speed, calm }) : null;
        if (!r) continue;
        ttsAudio = voiceEl; await playVoiceClip(r.mime, r.b64);
        if (gen !== ttsGen) return;
      }
      ttsFails = 0;
    } catch (e) {
      if (gen !== ttsGen) return;
      ttsFails++;
      toast('Voice: ' + cleanErr(e) + ' — reading with this PC’s voice for now', 'red');
      speakLocal(parts.slice(k));
    } finally { if (gen === ttsGen) { ttsBusy = false; ttsAudio = null; } }
  }
  function speak(text) {
    if (!CAN_TALK()) return;
    const t = forSpeech(text); if (!t) return;
    ttsStop(); pcStop(); if (CAN_SPEAK) try { speechSynthesis.cancel(); } catch (e) {}
    if (chatterGain) { try { chatterGain.gain.setTargetAtTime(0.35, actx.currentTime, 0.1); chatterGain.gain.setTargetAtTime(1, actx.currentTime + 2.5, 1.5); } catch (e) {} }
    if (HAS_TTS() && ttsFails < 3) ttsSay(passages(t, voiceCfg.engine === 'own' ? 170 : 500)); else if (pcVoiceOn()) pcSay(passages(t, 170)); else speakLocal(passages(t, 220));   // the own engine: a sentence or two at a time, so the first words come quickly while the rest is made
  }
  function hush() { ttsStop(); pcStop(); if (CAN_SPEAK) try { speechSynthesis.cancel(); } catch (e) {} }
  // ---- a voice on your PC, used from the web page (phone) ----
  // The page sends each passage to the PC over the phone link (sendTo); the PC's engine makes the clip
  // (cached there) and sends it back; the page plays it. Needs Poker Angel open on the PC.
  let pcBusy = false, pcGen = 0, pcReqId = 0, pcAudio = null;
  const pcWaiting = new Map();
  const pcLinked = () => !!(sendTo && sendTo.conn && sendTo.conn.open);
  const pcVoiceOn = () => !HAS_LIB && !!opts.pcVoice && pcLinked();
  function pcAsk(text, speed, calm) {
    return new Promise((res, rej) => {
      const id = ++pcReqId;
      const timer = setTimeout(() => { pcWaiting.delete(id); rej(new Error('The PC didn’t answer in time')); }, 90000);
      pcWaiting.set(id, { res, rej, timer });
      try { sendTo.conn.send({ t: 'tts', id, voice: opts.pcVoice, text, speed, calm: !!calm }); } catch (e) { clearTimeout(timer); pcWaiting.delete(id); rej(e); }
    });
  }
  function pcClip(m) {
    const w = pcWaiting.get(m.id); if (!w) return;
    clearTimeout(w.timer); pcWaiting.delete(m.id);
    if (m.t === 'ttsclip' && typeof m.b64 === 'string') w.res({ mime: m.mime || 'audio/wav', b64: m.b64 }); else w.rej(new Error(m.error || 'the PC could not make that clip'));
  }
  function pcStop() { pcGen++; pcBusy = false; if (pcAudio) { try { pcAudio.pause(); } catch (e) {} pcAudio = null; } }
  async function pcSay(parts) {
    const gen = ++pcGen; pcBusy = true;
    const calm = autoOn() && auto.calm, speed = calm ? 0.85 : (opts.speakRate || 1);
    try {
      let next = pcAsk(parts[0], speed, calm);
      for (let k = 0; k < parts.length; k++) {
        const r = await next; if (gen !== pcGen) return;
        next = k + 1 < parts.length ? pcAsk(parts[k + 1], speed, calm) : null;
        pcAudio = voiceEl; await playVoiceClip(r.mime, r.b64);
        if (gen !== pcGen) return;
      }
    } catch (e) {
      if (gen !== pcGen) return;
      toast('Your PC’s voice: ' + cleanErr(e) + ' — using this phone’s voice for now', 'red');
      speakLocal(parts);
    } finally { if (gen === pcGen) { pcBusy = false; pcAudio = null; } }
  }
  const voiceBusy = () => ttsBusy || pcBusy || voiceClipPlaying() || (CAN_SPEAK && speechSynthesis.speaking);
  const voiceQueued = () => !ttsBusy && CAN_SPEAK && !speechSynthesis.speaking && speechSynthesis.pending;
  // The voice picker under the table: this PC's voices (and a Try button), or the ElevenLabs voice from ⚙ Settings.
  function voiceSelHtml() {
    if (!CAN_TALK()) return '';
    const mine = voiceLib.filter(v => v.voiceId);
    if (HAS_TTS() || (mine.length && voiceCfg.engine === 'own')) {
      const cur = voiceCfg.ttsVoiceName || '';
      return '<span class="tr-voice">🎙 Voice: <select data-sel="coachVoice"><optgroup label="Your recorded voices">' + mine.map(v => '<option value="' + esc(v.name) + '"' + (v.name === cur ? ' selected' : '') + '>' + esc(v.name) + '</option>').join('') + '</optgroup>'
        + (voiceCfg.engine === 'eleven' && cur && !mine.some(v => v.name === cur) ? '<option value="' + esc(cur) + '" selected>' + esc(cur) + '</option>' : '')
        + '<option value="__pc">this PC’s built-in voice</option></select><button class="ghost tr-mini" data-act="ui:voicetry">🔈 Try</button></span>';
    }
    const vs = localVoices(), cur = pickVoice();
    const en = vs.filter(v => /^en/i.test(v.lang)), rest = vs.filter(v => !/^en/i.test(v.lang));
    const opt = v => '<option value="' + esc(v.name) + '"' + (cur && v.name === cur.name ? ' selected' : '') + '>' + esc(v.name.replace(/^Microsoft /, '')) + '</option>';
    const pcVoices = (!HAS_LIB && sendTo && sendTo.voices) ? sendTo.voices : [];
    const pcGroup = pcVoices.length ? '<optgroup label="' + (pcLinked() ? 'On your PC (linked)' : 'On your PC (not linked now)') + '">' + pcVoices.map(n => '<option value="__pcv:' + esc(n) + '"' + (opts.pcVoice === n ? ' selected' : '') + '>' + esc(n) + '</option>').join('') + '</optgroup>' : '';
    return '<span class="tr-voice">🔈 Voice: <select data-sel="voice">' + pcGroup + (mine.length ? '<optgroup label="Your recorded voices">' + mine.map(v => '<option value="__own:' + esc(v.name) + '">' + esc(v.name) + '</option>').join('') + '</optgroup><optgroup label="This PC’s built-in voices">' : '') + en.map(opt).join('') + (mine.length ? '</optgroup>' : '') + (rest.length ? '<optgroup label="Other languages">' + rest.map(opt).join('') + '</optgroup>' : '') + '</select>'
      + '<select data-sel="speakRate" title="Reading speed">' + [[0.8, 'slower'], [0.9, 'a little slower'], [1, 'normal speed'], [1.1, 'a little faster'], [1.25, 'faster']].map(([r, n]) => '<option value="' + r + '"' + ((opts.speakRate || 1) === r ? ' selected' : '') + '>' + n + '</option>').join('') + '</select>'
      + '<button class="ghost tr-mini" data-act="ui:voicetry">🔈 Try</button>'
      + (window.api && window.api.ttsSpeak ? '<span class="tr-dim">Want a natural voice, or a family member’s own? ⚙ Settings → Voice.</span>' : '') + '</span>';
  }
  // ---- 🎙 voices: record, name, assign ----
  // Several recordings, each with a name (Mum, Grandad, Dave…). On the desktop they live on this PC
  // (main.js voices:*) and are cloned on ElevenLabs as soon as a key is set, so they can be assigned to
  // the characters at the table (🎭 below) or chosen as the coach's voice in ⚙ Settings. One of them is
  // "my table voice": sent to the host when you join a table by code, so your character speaks as you.
  // On the web version (a phone) there is room for one recording, kept in the browser, and it can be
  // saved as a file and imported on the PC. Nothing is sent without the consent tick.
  const TVOICE_KEY = 'pokerangel.tablevoice', TVOICE_MAX_S = 60, TVOICE_MIN_S = 12;
  const VOICE_PARA = 'Evening, everyone. Shuffle up and deal. I’ve got a feeling about tonight — the cards have been kind to me all week, and I’m not about to argue with them. Pass the chips, pour me something warm, and let’s see a flop. If you bet into me, I might just call; if you check, I might just bet. Either way, no hard feelings — it’s only a game, and it’s a good one.';
  const VOICE_PARA2 = 'Right — who’s dealing? Three of us left and the pot’s already enormous! Honestly, I had no idea what he was holding. Was it a bluff? Maybe. Did it work? Absolutely not. Pass me the twenties, the fifties and that one red chip. Nine, ten, Jack… oh, come on, just one more. Well, that’s the end of that — same time next week? Lovely. Mine’s a tea, two sugars.';
  let myVoice = null; try { myVoice = JSON.parse(ls(TVOICE_KEY) || 'null'); } catch (e) { myVoice = null; }
  const HAS_LIB = typeof window !== 'undefined' && !!(window.api && window.api.voicesList);
  let voiceLib = [];                                                          // desktop: [{ name, mime, secs, when, hash, voiceId }]
  async function loadLib() {
    if (!HAS_LIB) return;
    try { voiceLib = await window.api.voicesList(); } catch (e) { voiceLib = []; }
    if (myVoice && !voiceLib.length) {                                        // a recording from before the library: keep it, under your name
      try { await window.api.voicesSave({ name: myName(), mime: myVoice.mime, b64: myVoice.b64, secs: myVoice.secs, hash: myVoice.hash }); voiceLib = await window.api.voicesList(); opts.myVoiceName = myName(); saveOpts(); localStorage.removeItem(TVOICE_KEY); myVoice = null; } catch (e) {}
    }
  }
  const CAN_RECORD = typeof navigator !== 'undefined' && !!navigator.mediaDevices && typeof window !== 'undefined' && !!(window.AudioContext || window.webkitAudioContext) && !(typeof WEB !== 'undefined' && WEB && !(typeof Peer === 'function'));
  const ON_PHONE = typeof navigator !== 'undefined' && /Android|iPhone|iPad|iPod/i.test(navigator.userAgent || '');
  const rec = { r: null, chunks: [], t0: 0, timer: 0, stream: null };
  const hashOf = str => { let h = 5381; for (let i = 0; i < str.length; i += 97) h = ((h << 5) + h + str.charCodeAt(i)) >>> 0; return h.toString(36) + str.length.toString(36); };
  const recName = () => { const el = $('trVoiceName'); const n = (el ? el.value : '').replace(/[^\w .'-]/g, '').trim().slice(0, 16); return n || myName(); };
  // A finished recording or an imported file: into the library (desktop) or the browser (web).
  async function keepVoice(v, name, append) {
    if (!HAS_LIB) { myVoice = v; try { ls(TVOICE_KEY, JSON.stringify(v)); } catch (e) { toast('Couldn’t keep the recording in this browser (too big) — it will still be sent this session', 'red'); } renderMain(); return; }
    try {
      const r = await window.api.voicesSave({ name, mime: v.mime, b64: v.b64, secs: v.secs, hash: v.hash, append: !!append });
      await loadLib();
      if (!opts.myVoiceName || !voiceLib.some(x => x.name === opts.myVoiceName)) { opts.myVoiceName = r.name; saveOpts(); }
      toast('🎙 ' + r.name + (r.takes > 1 ? ' (' + r.takes + ' takes)' : '') + (r.voiceId ? ' is ready to use' : r.cloneError ? ' saved — not cloned: ' + r.cloneError : ' saved — it will be cloned once ElevenLabs is set up in ⚙ Settings'), r.voiceId ? 'green' : '');
    } catch (e) { toast('Couldn’t save the recording: ' + cleanErr(e), 'red'); }
    renderMain();
  }
  // The recorder captures raw audio through Web Audio and writes a WAV itself. Phones' built-in
  // recorders (MediaRecorder) are unreliable — iPhones often hand back nothing — and a WAV is what the
  // voice engine wants anyway. 22.05 kHz mono, 16-bit: a 25-second take is about 1.1 MB.
  const REC_RATE = 22050;
  async function recStart(forName, append) {
    if (rec.r) return;
    const name = forName || recName(); rec.append = !!append;
    let ctx = null;
    try {
      ctx = new (window.AudioContext || window.webkitAudioContext)();             // made inside the tap, which iPhones require
      try { await ctx.resume(); } catch (e) {}
      rec.stream = await navigator.mediaDevices.getUserMedia({ audio: { echoCancellation: true, noiseSuppression: true, autoGainControl: true } });
      const src = ctx.createMediaStreamSource(rec.stream), proc = ctx.createScriptProcessor(4096, 1, 1), mute = ctx.createGain();
      mute.gain.value = 0;
      rec.pcm = []; rec.rate = ctx.sampleRate; rec.t0 = Date.now(); rec.name = name; rec.done = false; rec.peak = 0;
      proc.onaudioprocess = e => { if (!rec.pcm) return; const d = e.inputBuffer.getChannelData(0); rec.pcm.push(new Float32Array(d)); for (let i = 0; i < d.length; i += 64) { const v = Math.abs(d[i]); if (v > rec.peak) rec.peak = v; } };
      src.connect(proc); proc.connect(mute); mute.connect(ctx.destination);
      rec.r = { ctx, src, proc, mute, state: 'recording' };
      rec.timer = setInterval(() => { const el = $('trRecTime'); if (el) el.textContent = Math.round((Date.now() - rec.t0) / 1000) + ' s' + (rec.peak < 0.01 && Date.now() - rec.t0 > 3000 ? ' — no sound is reaching the microphone' : ''); if (Date.now() - rec.t0 > TVOICE_MAX_S * 1000) recStop(); }, 250);
      renderMain();
    } catch (e) {
      try { if (ctx) ctx.close(); } catch (x) {}
      const why = (e && e.name === 'NotAllowedError') ? 'The microphone was not allowed. Allow it for this site in the browser’s settings and try again.' : 'Couldn’t use the microphone: ' + cleanErr(e);
      toast(why, 'red'); if (sendTo) { sendTo.status = '❌ ' + why; renderMain(); }
    }
  }
  function recStop() {
    const r = rec.r; if (!r || rec.done) return;
    rec.done = true; clearInterval(rec.timer);
    const el = $('trRecTime'); if (el) el.textContent = 'finishing…';
    try { r.src.disconnect(); r.proc.disconnect(); r.mute.disconnect(); } catch (e) {}
    try { rec.stream.getTracks().forEach(t => t.stop()); } catch (e) {}
    try { r.ctx.close(); } catch (e) {}
    const chunks = rec.pcm || [], rate = rec.rate || 48000, secs = Math.round((Date.now() - rec.t0) / 1000);
    rec.r = null; rec.stream = null; rec.pcm = null;
    let n = 0; for (const c of chunks) n += c.length;
    if (!n || rec.peak < 0.005) {
      const why = !n ? 'The phone gave back no audio. Try once more; allow the microphone if asked.' : 'The recording was silent — the microphone picked up nothing. Check the phone isn’t muted and try again.';
      toast(why, 'red'); if (sendTo) sendTo.status = '❌ ' + why; renderMain(); return;
    }
    if (secs < TVOICE_MIN_S) { toast('That was only ' + secs + ' seconds — read the whole paragraph (about 20–30 seconds)', 'red'); if (sendTo) sendTo.status = 'Recorded ' + secs + ' s — too short, read the whole paragraph.'; renderMain(); return; }
    // join, downsample to 22.05 kHz, write a 16-bit WAV
    const all = new Float32Array(n); let o = 0; for (const c of chunks) { all.set(c, o); o += c.length; }
    const ratio = rate / REC_RATE, outN = Math.floor(n / ratio), out = new Int16Array(outN);
    for (let i = 0; i < outN; i++) { const p0 = i * ratio, i0 = Math.floor(p0), f = p0 - i0, v = all[i0] * (1 - f) + (all[Math.min(n - 1, i0 + 1)] || 0) * f; out[i] = Math.max(-32768, Math.min(32767, Math.round(v * 32767))); }
    const buf = new ArrayBuffer(44 + outN * 2), v = new DataView(buf), W = (off, str) => { for (let i = 0; i < str.length; i++) v.setUint8(off + i, str.charCodeAt(i)); };
    W(0, 'RIFF'); v.setUint32(4, 36 + outN * 2, true); W(8, 'WAVE'); W(12, 'fmt '); v.setUint32(16, 16, true); v.setUint16(20, 1, true); v.setUint16(22, 1, true); v.setUint32(24, REC_RATE, true); v.setUint32(28, REC_RATE * 2, true); v.setUint16(32, 2, true); v.setUint16(34, 16, true); W(36, 'data'); v.setUint32(40, outN * 2, true);
    new Int16Array(buf, 44).set(out);
    const bytes = new Uint8Array(buf); let bin = ''; for (let i = 0; i < bytes.length; i += 8192) bin += String.fromCharCode.apply(null, bytes.subarray(i, i + 8192));
    const b64 = btoa(bin);
    if (sendTo) sendTo.status = 'Recorded ' + secs + ' s (wav, ' + Math.round(bytes.length / 1024) + ' KB). Choose what it’s for and send.';
    keepVoice({ mime: 'audio/wav', b64, hash: hashOf(b64), secs, when: Date.now() }, rec.name, rec.append);
  }
  let recPlay = null;
  const playB64 = (mime, b64) => { if (recPlay) { try { recPlay.pause(); } catch (e) {} } recPlay = new Audio(blobUrl(mime, b64)); recPlay.play().catch(() => {}); };
  async function voiceData(name) {                                            // { mime, b64, hash, secs } for a library entry, or the browser's one
    if (!HAS_LIB) return myVoice;
    try { return await window.api.voicesGet({ name }); } catch (e) { return null; }
  }
  async function recPlayback(name) { const v = await voiceData(name); if (v) playB64(v.mime, v.b64); }
  async function recDelete(name) {
    if (!HAS_LIB) { myVoice = null; try { localStorage.removeItem(TVOICE_KEY); } catch (e) {} renderMain(); return; }
    try { await window.api.voicesDelete({ name }); } catch (e) {}
    if (opts.myVoiceName === name) { opts.myVoiceName = ''; }
    for (const k of Object.keys(opts.voiceAssign || {})) if (opts.voiceAssign[k] === name) delete opts.voiceAssign[k];
    saveOpts(); await loadLib(); renderMain();
  }
  async function recSave(name) {
    const v = await voiceData(name); if (!v) return;
    const ext = /mp4|m4a|aac/i.test(v.mime) ? 'm4a' : /ogg/i.test(v.mime) ? 'ogg' : /wav/i.test(v.mime) ? 'wav' : /mpeg|mp3/i.test(v.mime) ? 'mp3' : 'webm';
    const a = document.createElement('a'); a.href = 'data:' + v.mime + ';base64,' + v.b64; a.download = 'poker-angel-voice-' + String(name || myName() || 'me').replace(/\W+/g, '_') + '.' + ext;
    document.body.appendChild(a); a.click(); a.remove();
    toast(ON_PHONE ? 'Saved — share the file to your PC, then Import it in Poker Angel there' : 'Recording saved', 'green');
  }
  function recImport(file) {
    if (!file) return;
    let mime = String(file.type || '').toLowerCase();
    if (!mime || /x-m4a|aac/.test(mime)) mime = /\.(m4a|aac|mp4)$/i.test(file.name) ? 'audio/mp4' : /\.mp3$/i.test(file.name) ? 'audio/mpeg' : /\.wav$/i.test(file.name) ? 'audio/wav' : /\.ogg$/i.test(file.name) ? 'audio/ogg' : /\.webm$/i.test(file.name) ? 'audio/webm' : mime;
    if (!/^audio\/(webm|ogg|mp4|mpeg|wav|x-wav|flac)/.test(mime)) { toast('That isn’t an audio file the table voice can use (m4a, mp3, wav, ogg or webm)', 'red'); return; }
    if (file.size > 8 * 1024 * 1024) { toast('That recording is too big — keep it under a minute', 'red'); return; }
    const name = recName();
    const fr = new FileReader();
    fr.onload = () => {
      const m = String(fr.result).match(/^data:[^;]*;base64,(.+)$/); if (!m) return;
      const probe = new Audio('data:' + mime + ';base64,' + m[1]);
      const done = secs => keepVoice({ mime, b64: m[1], hash: hashOf(m[1]), secs: secs || 0, when: Date.now() }, name);
      probe.onloadedmetadata = () => done(isFinite(probe.duration) ? Math.round(probe.duration) : 0);
      probe.onerror = () => done(0);
    };
    fr.readAsDataURL(file);
  }
  async function recClone(name) {
    try { const r = await window.api.voicesClone({ name }); await loadLib(); toast('🎙 ' + name + ' is ready to use' + (r.reused ? '' : ''), 'green'); renderMain(); }
    catch (e) { toast(name + ': ' + cleanErr(e), 'red'); }
  }
  // What goes to the host when you join: the chosen library voice (desktop) or the browser's recording (web).
  async function voicePayload() {
    if (!opts.voiceConsent) return null;
    const v = HAS_LIB ? (opts.myVoiceName ? await voiceData(opts.myVoiceName) : null) : myVoice;
    return v ? { t: 'voice', name: myName(), mime: v.mime, b64: v.b64, hash: v.hash } : null;
  }
  // ---- 📲 voices from a phone ----
  // The PC opens a short code (a PeerJS id, like a table code). On the phone, the web page's Voices
  // block has "Send to a PC": type the code, name the voice, record, send. The PC saves it into the
  // library (and clones it) — as many as you like, one after another. Direct phone-to-PC; the PeerJS
  // server only introduces them.
  let inbox = null;                // PC: { code, peer, got: [] }
  let sendTo = null;               // phone: { code, peer, conn, status, bots }
  // The PC's phone code is permanent (kept in the options), so the phone can send a voice any time
  // Poker Angel is open — no need to press anything here first.
  const phoneCode = () => { if (!opts.phoneCode) { opts.phoneCode = newCode(); saveOpts(); } return opts.phoneCode; };
  async function applyVoiceUse(name, use) {
    if (!use) return '';
    if (use === 'coach') { const id = libVoiceId(name); if (!id) return 'saved — it will be the coach’s voice once it is ready'; await window.api.setTts({ voice: id, voiceName: name }); voiceChanged(); return 'now the coach’s voice'; }
    if (use === 'mine') { opts.myVoiceName = name; saveOpts(); return 'now your table voice'; }
    if (/^bot:/.test(use)) { const bot = use.slice(4); opts.voiceAssign = opts.voiceAssign || {}; opts.voiceAssign[bot] = name; saveOpts(); return 'now ' + bot + '’s voice'; }
    return '';
  }
  function inboxOpen() {
    if (!HAS_LIB || inbox || typeof Peer !== 'function') return;
    const code = phoneCode(), peer = new Peer(PEER_PREFIX + 'v-' + code.toLowerCase(), PEER_OPTS);
    inbox = { code, peer, got: [], status: 'Opening…' };
    peer.on('open', () => { if (inbox && inbox.peer === peer) { inbox.status = ''; renderMain(); } });
    peer.on('connection', conn => {
      conn.on('open', () => { try { conn.send({ t: 'welcome', bots: BOTS.slice(), voices: voiceLib.map(v => v.name), engine: voiceCfg.engine }); } catch (e) {} });
      conn.on('data', async m => {
        if (!m || typeof m !== 'object') return;
        if (m.t === 'tts') {                                      // the phone wants a line spoken in one of this PC's voices
          const id = libVoiceId(String(m.voice || '')), text = String(m.text || '').slice(0, 600);
          if (!id || !HAS_TTS() || !text) { try { conn.send({ t: 'ttsfail', id: m.id, error: !id ? 'no such voice on the PC' : 'the PC’s voice engine is off' }); } catch (e) {} return; }
          try { const clip = await window.api.ttsSay({ voiceId: id, text, speed: Math.max(0.7, Math.min(1.3, Number(m.speed) || 1)) }); conn.send({ t: 'ttsclip', id: m.id, mime: clip.mime, b64: clip.b64 }); }
          catch (e) { try { conn.send({ t: 'ttsfail', id: m.id, error: cleanErr(e) }); } catch (x) {} }
          return;
        }
        if (m.t === 'use') {                                      // a voice already on the PC, given a job from the phone
          const name = String(m.name || '').slice(0, 16); if (!voiceLib.some(v => v.name === name)) return;
          const what = await applyVoiceUse(name, String(m.use || '')); try { conn.send({ t: 'ok', name, cloned: true, what }); } catch (e) {} renderMain(); return;
        }
        if (m.t !== 'voicefile' || typeof m.b64 !== 'string' || m.b64.length > 12e6) return;
        const name = String(m.name || '').replace(/[^\w .'-]/g, '').trim().slice(0, 16) || 'Voice';
        try {
          const r = await window.api.voicesSave({ name, mime: String(m.mime || ''), b64: m.b64, secs: Number(m.secs) || 0, hash: String(m.hash || ''), append: !!m.append });
          await loadLib(); if (inbox) inbox.got.push(name);
          const what = await applyVoiceUse(name, String(m.use || ''));
          try { conn.send({ t: 'ok', name, cloned: !!r.voiceId, error: r.cloneError || '', what }); } catch (e) {}
          toast('📲 ' + name + ' received from the phone' + (r.voiceId ? ' and ready' : '') + (what ? ' — ' + what : ''), 'green'); renderMain();
        } catch (e) { try { conn.send({ t: 'fail', error: cleanErr(e) }); } catch (x) {} toast('📲 ' + name + ': ' + cleanErr(e), 'red'); }
      });
    });
    peer.on('disconnected', () => { if (inbox && inbox.peer === peer && !peer.destroyed) { try { peer.reconnect(); } catch (e) {} } });   // the signalling server dropped us: register again under the same code
    peer.on('error', e => { if (!inbox || inbox.peer !== peer) return; if (e && e.type === 'unavailable-id') { opts.phoneCode = ''; inboxClose(true); inboxOpen(); return; } if (/network|server|socket|disconnected/i.test(e.type || '')) { inbox.status = 'Reconnecting…'; try { peer.reconnect(); } catch (x) {} renderMain(); return; } inbox.status = 'Connection trouble: ' + (e && (e.type || e.message)); renderMain(); });
    renderMain();
  }
  // Once a minute: if the listener has died, bring it back.
  setInterval(() => { try { if (!HAS_LIB || typeof Peer !== 'function') return; if (!inbox) return inboxOpen(); if (inbox.peer.destroyed) { inbox = null; inboxOpen(); } else if (inbox.peer.disconnected) { inbox.status = 'Reconnecting…'; inbox.peer.reconnect(); } else if (inbox.status && inbox.peer.open) { inbox.status = ''; renderMain(); } } catch (e) {} }, 15000);
  function inboxClose(quiet) { if (!inbox) return; try { inbox.peer.destroy(); } catch (e) {} inbox = null; if (!quiet) renderMain(); }
  function inboxHtml() {
    if (!HAS_LIB || typeof Peer !== 'function') return '';
    if (!inbox) return '<div class="tr-inbox"><b>📲 Your phone code: <span class="tr-code">' + esc(phoneCode()) + '</span></b> <span class="tr-dim">Opening…</span> <button class="ghost tr-mini" data-act="rec:inbox">Retry</button></div>';
    return '<div class="tr-inbox"><b>📲 Your phone code: <span class="tr-code">' + esc(inbox.code) + '</span></b>' + (inbox.status ? ' <span class="tr-dim">' + esc(inbox.status) + '</span>' : '')
      + '<div class="tr-dim">Everything can be done from the phone: open <b>' + esc(PUBLIC_URL) + '</b> → 🎙 Voices → Send to a PC, enter this code once, then record each voice, say what it’s for (the coach, your seat, a character) and send. It arrives here' + (HAS_TTS() ? ' and is ready' : '') + ' straight away. The code stays the same.</div>'
      + (inbox.got.length ? '<div class="tr-dim">Received: ' + esc(inbox.got.join(', ')) + '</div>' : '') + '</div>';
  }
  // the phone side
  const PCCODE_KEY = 'pokerangel.pccode';
  function sendConnect(code) {
    code = String(code || '').trim().toUpperCase();
    if (!/^[A-Z2-9]{5}$/.test(code)) { toast('Enter the 5-letter code shown on the PC', 'red'); return; }
    if (typeof Peer !== 'function') { toast('The connection library didn’t load', 'red'); return; }
    if (sendTo) { try { sendTo.peer.destroy(); } catch (e) {} }
    const peer = new Peer(PEER_OPTS);
    sendTo = { code, peer, conn: null, status: 'Connecting to PC ' + code + '…', bots: [], voices: [] }; try { ls(PCCODE_KEY, code); } catch (e) {} renderMain();
    const giveUp = setTimeout(() => { if (sendTo && sendTo.peer === peer && !sendTo.conn) { sendTo.status = 'No PC is listening under ' + code + ' — press 📲 Receive voices on the PC first.'; renderMain(); } }, 15000);
    peer.on('open', () => {
      const conn = peer.connect(PEER_PREFIX + 'v-' + code.toLowerCase(), { reliable: true });
      conn.on('open', () => { clearTimeout(giveUp); if (sendTo && sendTo.peer === peer) { sendTo.conn = conn; sendTo.status = ''; renderMain(); } });
      conn.on('data', m => { if (!m || !sendTo) return;
        if (m.t === 'welcome') { sendTo.bots = m.bots || []; sendTo.voices = m.voices || []; sendTo.status = ''; if (!opts.pcVoice && sendTo.voices.length && !opts.voice) { opts.pcVoice = sendTo.voices[0]; saveOpts(); } renderMain(); return; }
        if (m.t === 'ttsclip' || m.t === 'ttsfail') return pcClip(m);
        if (m.t === 'ok') { clearTimeout(sendTo.ackTimer); sendTo.sentAt = 0; sendTo.status = '✅ ' + m.name + ' is on the PC' + (m.cloned ? ' and ready' : '') + (m.what ? ' — ' + m.what : '') + '. Record the next one, or you’re done.'; if (!sendTo.voices.includes(m.name)) sendTo.voices.push(m.name); myVoice = null; try { localStorage.removeItem(TVOICE_KEY); } catch (e) {} }
        else if (m.t === 'fail') sendTo.status = '❌ ' + m.error; renderMain(); });
      conn.on('close', () => { if (sendTo && sendTo.peer === peer) { sendTo.status = 'The connection to the PC closed — tap Connect again.'; sendTo.conn = null; renderMain(); } });
      conn.on('error', e => { if (sendTo && sendTo.peer === peer) { sendTo.status = '❌ Connection error: ' + (e && (e.message || e.type) || e); renderMain(); } });
      conn.on('iceStateChanged', st => { if (sendTo && sendTo.peer === peer && /failed|disconnected/.test(String(st))) { sendTo.status = '❌ The link to the PC ' + st + ' — same Wi‑Fi as the PC, then Connect again.'; renderMain(); } });
    });
    peer.on('error', e => { clearTimeout(giveUp); if (sendTo && sendTo.peer === peer) { sendTo.status = e && e.type === 'peer-unavailable' ? 'No PC is listening under ' + code + ' — press 📲 Receive voices on the PC first.' : 'Couldn’t connect: ' + (e && (e.type || e.message)); renderMain(); } });
  }
  function sendVoice() {
    if (!sendTo || !sendTo.conn || !sendTo.conn.open) { toast('Connect to the PC first', 'red'); return; }
    if (!myVoice) { toast('Record a voice first', 'red'); return; }
    const name = recName(), useEl = $('trVoiceUse'), use = useEl ? useEl.value : 'coach';
    try { sendTo.conn.send({ t: 'voicefile', name, mime: myVoice.mime, b64: myVoice.b64, secs: myVoice.secs, hash: myVoice.hash, use }); sendTo.status = 'Sending ' + name + ' (' + Math.round(myVoice.b64.length * 0.75 / 1024) + ' KB)…'; sendTo.sentAt = Date.now(); renderMain();
      clearTimeout(sendTo.ackTimer); sendTo.ackTimer = setTimeout(() => { if (sendTo && sendTo.sentAt && /^Sending/.test(sendTo.status || '')) { sendTo.status = '❌ The PC didn’t confirm within 90 seconds. Make sure the phone and the PC are on the same Wi‑Fi, tap Connect again, and send again.'; renderMain(); } }, 90000); }
    catch (e) { toast('Couldn’t send: ' + cleanErr(e), 'red'); }
  }
  function useSel(bots) {
    return '<select id="trVoiceUse"><option value="coach">the coach’s voice (and the Angel’s)</option><option value="mine">my own seat at the table</option>' + (bots || []).map(b => '<option value="bot:' + esc(b) + '">the character ' + esc(b) + '</option>').join('') + '<option value="">just keep it on the PC</option></select>';
  }
  function sendHtml() {
    if (HAS_LIB || !CAN_RECORD || typeof Peer !== 'function') return '';
    const con = sendTo && sendTo.conn;
    return '<div class="tr-inbox"><b>📲 Send to the PC</b> <span class="tr-dim">The code is on the PC’s Play menu under 🎙 Voices — it never changes. Enter it once; then name a voice, record, choose what it’s for, send.</span>'
      + '<div class="tr-row"><input id="trSendCode" placeholder="PC code" maxlength="5" style="width:110px;text-transform:uppercase" value="' + esc(sendTo ? sendTo.code : (ls(PCCODE_KEY) || '')) + '" /><button class="' + (con ? 'ghost' : '') + '" data-act="rec:connect">' + (con ? 'Connected ✓' : 'Connect') + '</button></div>'
      + (con ? '<div class="tr-row"><input id="trVoiceName" placeholder="Name this voice (e.g. Mum)" maxlength="16" style="width:170px" /><label class="tr-dim">Use it as ' + useSel(sendTo.bots) + '</label>'
        + (myVoice ? '<button data-act="rec:send">📤 Send to PC</button>' : '<span class="tr-dim">— record above, then send</span>') + '</div>'
        + (sendTo.voices && sendTo.voices.length ? '<div class="tr-row"><span class="tr-dim">Already on the PC:</span>' + sendTo.voices.map(v => '<button class="ghost tr-mini" data-act="rec:usepc" data-name="' + esc(v) + '" title="Give this voice the job chosen above">' + esc(v) + '</button>').join('') + '</div>' : '') : '')
      + (sendTo && sendTo.status ? '<div class="tr-dim">' + esc(sendTo.status) + '</div>' : '') + '</div>';
  }
  function usePcVoice(name) { if (!sendTo || !sendTo.conn || !sendTo.conn.open) return; const useEl = $('trVoiceUse'); try { sendTo.conn.send({ t: 'use', name, use: useEl ? useEl.value : 'coach' }); sendTo.status = 'Telling the PC…'; renderMain(); } catch (e) {} }
  const PUBLIC_URL = 'frankthedog.github.io/poker-angel';
  const libVoiceId = name => { const v = voiceLib.find(x => x.name === name); return v && v.voiceId || ''; };
  function voiceRecHtml() {
    if (!CAN_RECORD) return '';
    const fmtWhen = w => new Date(w).toLocaleDateString(undefined, { day: 'numeric', month: 'short' });
    const recRow = rec.r ? '<button class="fold" data-act="rec:stop">⏹ Stop</button><span class="tr-dim">Recording ' + esc(rec.name || '') + '… <b id="trRecTime">0 s</b></span>'
      : (HAS_LIB ? '<input id="trVoiceName" placeholder="Name this voice (e.g. Mum)" maxlength="16" style="width:170px" value="' + esc(voiceLib.length ? '' : myName()) + '" />' : '')
        + '<button data-act="rec:start">🎙 Record</button><button class="ghost" data-act="rec:import">📂 Import a recording</button><input type="file" id="trRecFile" accept="audio/*,.m4a,.mp3,.wav,.ogg,.webm" style="display:none" />';
    let list = '';
    if (HAS_LIB) {
      const canClone = HAS_TTS() || voiceCfg.hasTtsKey || voiceCfg.engine === 'own';
      list = voiceLib.length ? '<div class="tr-voices">' + voiceLib.map(v => '<div class="tr-vrow"><label title="Sent to the host when you join a table — your character speaks as you"><input type="radio" name="trMyVoice" data-myvoice="' + esc(v.name) + '"' + (opts.myVoiceName === v.name ? ' checked' : '') + ' /> mine</label>'
        + '<b>' + esc(v.name) + '</b><span class="tr-dim">' + (v.takes > 1 ? v.takes + ' takes · ' : '') + (v.secs ? v.secs + ' s · ' : '') + fmtWhen(v.when) + ' · ' + (v.voiceId ? '✅ ready' : canClone ? '<button class="ghost tr-mini" data-act="rec:clone" data-name="' + esc(v.name) + '">Make it a voice</button>' : 'saved; becomes a voice once a voice engine is set up (⚙ Settings → Voice)') + '</span>'
        + '<span class="tr-vbtns">' + (v.takes < 3 && !rec.r ? '<button class="ghost tr-mini" data-act="rec:more" data-name="' + esc(v.name) + '" title="Record a second, more varied paragraph — a noticeably better clone">➕ take</button>' : '') + '<button class="ghost tr-mini" data-act="rec:play" data-name="' + esc(v.name) + '">▶</button><button class="ghost tr-mini" data-act="rec:save" data-name="' + esc(v.name) + '" title="Save as a file">⬇</button><button class="ghost tr-mini" data-act="rec:delete" data-name="' + esc(v.name) + '" title="Delete this voice (and its clone)">✖</button></span></div>').join('') + '</div>'
        : '<div class="tr-dim">No voices yet.</div>';
    } else if (myVoice) {
      list = '<div class="tr-vrow"><b>My table voice</b><span class="tr-dim">' + (myVoice.secs ? 'Recorded ' + myVoice.secs + ' s on ' : 'Imported on ') + fmtWhen(myVoice.when) + '</span><span class="tr-vbtns"><button class="ghost tr-mini" data-act="rec:play">▶ Play back</button><button class="ghost tr-mini" data-act="rec:save">⬇ Save</button><button class="ghost tr-mini" data-act="rec:delete">Delete</button></span></div>';
    }
    return '<div class="tr-q tr-rec"><b>🎙 Voices</b> — ' + (HAS_LIB ? 'record as many as you like (you, family, friends), each with a name. Each becomes a voice on ' + (voiceCfg.engine === 'own' ? 'your own voice engine on this PC' : 'your ElevenLabs account') + ', then you can give it to any character at the table (🎭 below), choose it as the coach’s voice in ⚙ Settings → Voice, or mark it “mine” to be sent to a table you join. ' : 'read the paragraph once (about 25 seconds), tap Stop, then send it to the PC below — the PC turns it into a voice itself. Nothing to sign up for. ')
      + (ON_PHONE ? 'You’re on a phone — a good microphone. Record here and send each voice straight to the PC (📲 below), or join a table from this phone.' : 'A phone’s microphone is usually better than a PC’s: press 📲 Receive voices from a phone below, then record on the phone and each voice arrives here.')
      + '<div class="tr-para">' + esc(rec.r && rec.append ? VOICE_PARA2 : VOICE_PARA) + '</div>' + (rec.r && rec.append ? '<div class="tr-dim">Second take: a different paragraph, with questions and numbers, so the clone hears more of the voice.</div>' : '') + '<div class="tr-row">' + recRow + '</div>' + list
      + inboxHtml() + sendHtml()
      + '<label class="tr-dim"><input type="checkbox" data-opt="voiceConsent"' + (opts.voiceConsent ? ' checked' : '') + ' /> I agree that a recording marked “mine” may be sent to the host of a table I join, so their Poker Angel can voice my character at that table.</label></div>'
      + assignHtml();
  }
  // 🎭 which voice each character at the table speaks with (the bots by name; friends bring their own)
  function assignHtml() {
    if (!HAS_LIB) return '';
    const ready = voiceLib.filter(v => v.voiceId);
    if (!ready.length) return '';
    const names = (g ? g.players.filter(p => p.style).map(p => p.name) : []).concat(BOTS).filter((n, i, arr) => arr.indexOf(n) === i);
    const assign = opts.voiceAssign || {};
    return '<div class="tr-q tr-assign"><b>🎭 Who speaks with which voice</b> — the characters at the table talk in these voices (🗣 Table chatter). The coach’s own voice is set in ⚙ Settings → Voice, where your recordings are listed too (★).'
      + '<div class="tr-grid2">' + names.map(n => '<label>' + esc(n) + ' <select data-sel="assign" data-name="' + esc(n) + '"><option value="">a stock voice</option>' + ready.map(v => '<option value="' + esc(v.name) + '"' + (assign[n] === v.name ? ' selected' : '') + '>' + esc(v.name) + '</option>').join('') + '</select></label>').join('') + '</div></div>';
  }

  // ---- 🗣 table talk and 🎧 room sound ----
  // Players who are out of the hand (and everyone between hands) occasionally say a short, harmless
  // line — in their own recorded voice if they sent one, or a stock voice for a bot — played softly
  // from their side of the table. Never while the coaching is talking; by default never while it's
  // your turn. One line every half a minute or so: atmosphere, not a conversation. The lines come from
  // a fixed bank, so after the first time each is served from the cache and costs nothing.
  const REMARKS = {
    watching: ['Glad I’m out of this one.', 'Ooh, that’s a big bet.', 'Here we go.', 'I’d be sweating that.', 'Somebody’s got something.', 'Nice pot.', 'Come on, show us a river card.', 'Chips flying tonight.', 'I’ll get the next one.', 'Interesting.', 'Take your time.', 'This is getting expensive.', 'I’m happy watching this one.', 'Go on then.'],
    between: ['Nice hand.', 'Well played.', 'Unlucky.', 'That river!', 'Shuffle up.', 'Anyone for a cuppa?', 'Right, next one.', 'I’m card dead tonight.', 'Easy game, this.', 'That’s poker.', 'Ouch.', 'Deal me a decent one for once.', 'Same again.', 'Who’s dealing?', 'I need a better seat.', 'The cards owe me.'],
    won: ['Thank you very much.', 'Ship it.', 'About time.', 'Told you.', 'I’ll take that.', 'Lovely.'],
    lost: ['Unbelievable.', 'Of course.', 'Every time.', 'Nice one.', 'I’ll remember that.', 'Typical.'],
  };
  function pickRemark(kind, recent) {
    const bank = REMARKS[kind] || REMARKS.between, fresh = bank.filter(l => (recent || []).indexOf(l) < 0);
    const from = fresh.length ? fresh : bank; return from[Math.floor(Math.random() * from.length)];
  }
  const FEMALE = /^(Mia|Zara|Rosa|Priya|Gloria|Lena)$/;
  let actx = null, chatterGain = null, roomNodes = null, chatterTimer = 0, chatterBusy = false, stockVoices = null, recentSaid = [];
  function audioCtx() {
    if (!actx) { try { actx = new (window.AudioContext || window.webkitAudioContext)(); chatterGain = actx.createGain(); chatterGain.gain.value = 1; chatterGain.connect(actx.destination); } catch (e) { return null; } }
    if (actx.state === 'suspended') actx.resume().catch(() => {});
    return actx;
  }
  const panOf = seat => { try { const x = layout().seat[view(seat)][0]; return Math.max(-0.85, Math.min(0.85, (x - 50) / 60)); } catch (e) { return 0; } };
  const chatterVol = () => ({ soft: 0.22, normal: 0.38, loud: 0.6 })[opts.chatterVol || 'soft'] || 0.22;
  async function playClip(b64, mime, gain, pan) {
    const ctx = audioCtx(); if (!ctx) return;
    const bin = atob(b64), buf = new Uint8Array(bin.length); for (let i = 0; i < bin.length; i++) buf[i] = bin.charCodeAt(i);
    const audio = await ctx.decodeAudioData(buf.buffer);
    await new Promise(res => {
      const src = ctx.createBufferSource(); src.buffer = audio;
      const g1 = ctx.createGain(); g1.gain.value = gain;
      const pn = ctx.createStereoPanner ? ctx.createStereoPanner() : null; if (pn) pn.pan.value = pan;
      src.connect(g1); if (pn) { g1.connect(pn); pn.connect(chatterGain); } else g1.connect(chatterGain);
      src.onended = res; src.start();
    });
  }
  // Who may chatter now, and in which voice.
  function chatterCandidates() {
    if (!g || me < 0) return [];
    return g.players.map((p, j) => ({ p, j })).filter(o => o.j !== me && (g.over || o.p.folded || o.p.out))
      .filter(o => !(room && room.conns && Array.from(room.conns.values()).some(c => c.seat === o.j && c.talk === false)))   // a friend who asked for their character to stay quiet
      .map(o => ({ seat: o.j, name: o.p.name, voiceId: voiceFor(o.p) })).filter(o => o.voiceId);
  }
  function voiceFor(p) {
    if (room && room.voices && room.voices[p.name]) return room.voices[p.name];
    const chosen = opts.voiceAssign && opts.voiceAssign[p.name] && libVoiceId(opts.voiceAssign[p.name]); if (chosen) return chosen;
    if (!p.style || !stockVoices || !stockVoices.length) return null;              // a person without a recording stays silent
    const fem = FEMALE.test(p.name), pool = stockVoices.filter(v => fem ? /female/i.test(v.about) : /(^|[^e])male/i.test(v.about));
    const list = pool.length ? pool : stockVoices;
    let h = 0; for (const ch of p.name) h = (h * 31 + ch.charCodeAt(0)) >>> 0;
    return list[h % list.length].id;
  }
  // ---- how chatty: Off · Murmurs · Chatty · Banter ----
  // Murmurs: the fixed bank, rarely. Chatty: lines the AI writes for each character (the nit grumbles,
  // the maniac brags, a friend is just friendly), more often, and reactions to what happens — an
  // all-in, a huge pot, someone arriving — plus the odd word to you by name. Banter: all that, more
  // often, with short two-line exchanges between two characters. Still never over the coaching, and by
  // default never while you're deciding. The AI's lines are kept for a fortnight per character, and
  // every spoken line is cached, so neither the AI nor the voice is paid for twice.
  const TALK_LEVELS = [['off', 'Off', 'Silence apart from the coaching.'], ['murmur', 'Murmurs', 'The odd short line, now and then.'], ['chatty', 'Chatty', 'Lines written for each character, reactions to big moments, a word to you by name.'], ['banter', 'Banter', 'Chatty, more often, with short exchanges between players.']];
  const talkLevel = () => TALK_LEVELS.some(l => l[0] === opts.talk) ? opts.talk : (opts.chatter ? 'murmur' : 'off');
  const talkIdx = () => TALK_LEVELS.findIndex(l => l[0] === talkLevel());
  const chatterOn = () => talkIdx() > 0 && HAS_TTS() && !isGuest() && !(room && room.web);
  const TALK_KEY = 'pokerangel.talk.v1', TALK_TTL = 14 * 86400000;
  let talkBanks = {}; try { talkBanks = JSON.parse(ls(TALK_KEY) || '{}') || {}; } catch (e) { talkBanks = {}; }
  const talkBusy = new Set();
  const TALK_SYSTEM = 'You write table talk for one character at a friendly home poker game in Britain. Reply with JSON only — an object with these keys, each an array of short spoken lines (at most 12 words each, plain text, no quotation marks, no emoji): '
    + '"watching" (8 lines, said while sitting out a hand others are playing), "between" (8, said between hands), "won" (6, having just won a pot), "lost" (6, having just lost one), "allin" (6, someone has just gone all-in), "bigpot" (6, a huge pot has just been won), "greet" (4, welcoming a newcomer called {player}), "toPlayer" (6, a friendly word to the person at the table called {player}), '
    + 'and "banter" (6 objects {"a": "...", "b": "..."}: a line this character says to another player and a plausible one-line reply from them). '
    + 'RULES: never mention specific cards, hands, odds, or what anyone should do or should have done — nothing that could coach or give a hand away. No swearing, no cruelty; teasing is fine. Use {player} exactly as written where a name belongs and nowhere else. Stay in character throughout.';
  const bankKey = p => p.style ? p.style + ':' + (p.level || '') : 'friend';
  const persona = p => p.style ? 'The character: ' + p.name + ', a ' + styleName(p.style) + ' player' + (p.level ? ' (' + p.level + ')' : '') + '. How they play: ' + (STYLE_HOW[p.style] || STYLES[p.style].label) + '. Give them a voice to match — the way they play is the way they talk.'
    : 'The character: a friend who has come round to play — warm, relaxed, a bit of a tease, happy to be here.';
  const cleanLine = l => String(l || '').replace(/["“”]/g, '').replace(/\s+/g, ' ').trim().slice(0, 90);
  async function ensureBank(p) {
    const key = bankKey(p), have = talkBanks[key];
    if (have && Date.now() - have.when < TALK_TTL) return have.bank;
    if (!HAS_AI || talkBusy.has(key) || !(window.api && window.api.draft)) return null;
    talkBusy.add(key);
    try {
      const txt = await window.api.draft({ system: TALK_SYSTEM, user: persona(p) });
      const j = JSON.parse(txt.slice(txt.indexOf('{'), txt.lastIndexOf('}') + 1)), bank = {};
      for (const k of ['watching', 'between', 'won', 'lost', 'allin', 'bigpot', 'greet', 'toPlayer']) bank[k] = (Array.isArray(j[k]) ? j[k] : []).map(cleanLine).filter(l => l && !/\b(fold|raise|call|bluff|flush|straight|ace|king|queen|jack|pair|odds)\b/i.test(l)).slice(0, 10);
      bank.banter = (Array.isArray(j.banter) ? j.banter : []).map(x => x && ({ a: cleanLine(x.a), b: cleanLine(x.b) })).filter(x => x && x.a && x.b).slice(0, 8);
      if (bank.watching.length + bank.between.length < 6) throw new Error('too few lines');
      talkBanks[key] = { when: Date.now(), bank }; try { ls(TALK_KEY, JSON.stringify(talkBanks)); } catch (e) {}
      return bank;
    } catch (e) { console.error('table talk', e); talkBanks[key] = { when: Date.now() - TALK_TTL + 3600000, bank: null }; return null; }   // try again in an hour
    finally { talkBusy.delete(key); }
  }
  function freshTalk() { talkBanks = {}; try { localStorage.removeItem(TALK_KEY); } catch (e) {} toast('The characters will get fresh lines from the AI', 'green'); }
  // The line for a character and a moment: the AI's bank at Chatty and above, else the fixed one.
  function lineFor(p, kind, bank) {
    const b = talkIdx() >= 2 && bank ? bank : null, fallback = { allin: 'watching', bigpot: 'between', greet: 'between', toPlayer: 'between' };
    let pool = b && b[kind] && b[kind].length ? b[kind] : (REMARKS[kind] || REMARKS[fallback[kind] || 'between']);
    const fresh = pool.filter(l => recentSaid.indexOf(l) < 0); pool = fresh.length ? fresh : pool;
    return pool[Math.floor(Math.random() * pool.length)].replace(/\{player\}/g, myName());
  }
  // moments worth a word: queued by the game, spoken within a few seconds if the level allows
  let talkEvents = [];
  function talkEvent(kind, ctx) {
    if (!chatterOn()) return;
    const chance = [0, 0.25, 0.65, 0.9][talkIdx()] || 0;
    if (Math.random() > chance) return;
    talkEvents.push({ kind, ctx: ctx || {}, at: Date.now() });
    clearTimeout(chatterTimer); chatterTimer = setTimeout(chatterTick, 1500 + Math.random() * 2500);
  }
  function chatterSchedule() {
    clearTimeout(chatterTimer);
    if (!chatterOn()) return;
    const base = [0, 45000, 24000, 15000][talkIdx()] || 30000;
    chatterTimer = setTimeout(chatterTick, base * (0.6 + Math.random() * 0.8));
  }
  async function sayAs(who, line) {
    const clip = await window.api.ttsSay({ voiceId: who.voiceId, text: line, speed: 1 });
    if (!clip || voiceBusy()) return false;
    if (isHost()) for (const [conn] of room.conns) { if (conn.open) try { conn.send({ t: 'say', seat: who.seat, mime: clip.mime, b64: clip.b64 }); } catch (e) {} }
    await playClip(clip.b64, clip.mime, chatterVol(), panOf(who.seat));
    return true;
  }
  async function chatterTick() {
    if (!chatterOn()) return;
    try {
      if (!shown || tab !== 'play' || !g || voiceBusy() || chatterBusy || (opts.chatterQuiet !== false && !g.over && g.toAct === me)) return;
      if (!stockVoices) { try { stockVoices = (await window.api.ttsVoices()).filter(v => !v.own); } catch (e) { stockVoices = []; } }
      const cands = chatterCandidates(); if (!cands.length) { talkEvents = []; return; }
      talkEvents = talkEvents.filter(ev => Date.now() - ev.at < 12000);
      const ev = talkEvents.shift();
      let pool = cands; if (ev && ev.ctx.seat != null) pool = cands.filter(c => c.seat !== ev.ctx.seat); if (!pool.length) pool = cands;
      const who = pool[Math.floor(Math.random() * pool.length)], p = g.players[who.seat];
      const bank = talkIdx() >= 2 ? await ensureBank(p) : null;
      let kind = ev ? ev.kind : (g.over ? 'between' : 'watching');
      if (!ev && g.over && g.result) { if (g.result.wins.some(w => w.i === who.seat)) kind = 'won'; else if (g.result.showdown && !p.folded && Math.random() < 0.6) kind = 'lost'; }
      if (!ev && talkIdx() >= 2 && Math.random() < 0.15) kind = 'toPlayer';
      chatterBusy = true;
      // Banter: this character says something to another, who answers in their own voice.
      if (!ev && talkIdx() >= 3 && bank && bank.banter.length && pool.length > 1 && Math.random() < 0.35) {
        const other = pool.filter(c => c.seat !== who.seat)[Math.floor(Math.random() * (pool.length - 1))], pair = bank.banter[Math.floor(Math.random() * bank.banter.length)];
        if (await sayAs(who, pair.a.replace(/\{player\}/g, g.players[other.seat].name))) { await new Promise(r => setTimeout(r, 500)); if (!voiceBusy()) await sayAs(other, pair.b.replace(/\{player\}/g, p.name)); }
        return;
      }
      let line = lineFor(p, kind, bank);
      if (ev && ev.kind === 'greet' && ev.ctx.name) line = line.replace(myName(), ev.ctx.name);
      recentSaid = recentSaid.concat(line).slice(-12);
      await sayAs(who, line);
    } catch (e) { console.error('chatter', e); }
    finally { chatterBusy = false; chatterSchedule(); }
  }
  // A guest hears what the host's table says (its own seat is at the bottom, so the panning is its own).
  function onSay(m) { if (talkLevel() === 'off' || !m || typeof m.b64 !== 'string' || m.b64.length > 2e6) return; playClip(m.b64, String(m.mime || 'audio/mpeg'), chatterVol(), panOf(Number(m.seat) || 0)).catch(() => {}); }
  // Room sound: a low murmur and the odd riffle of chips, synthesised — no recording, nothing to download.
  const roomVol = () => ({ soft: 0.5, normal: 1, loud: 1.6 })[opts.roomVol || 'soft'] || 0.5;
  function roomStart() {
    const ctx = audioCtx(); if (!ctx || roomNodes) return;
    const len = ctx.sampleRate * 4, buf = ctx.createBuffer(2, len, ctx.sampleRate);
    for (let ch = 0; ch < 2; ch++) { const d = buf.getChannelData(ch); let last = 0; for (let i = 0; i < len; i++) { const w = Math.random() * 2 - 1; last = (last + 0.02 * w) / 1.02; d[i] = last * 3.5; } }   // brown-ish noise
    const src = ctx.createBufferSource(); src.buffer = buf; src.loop = true;
    const lp = ctx.createBiquadFilter(); lp.type = 'lowpass'; lp.frequency.value = 420;
    const murmur = ctx.createBiquadFilter(); murmur.type = 'bandpass'; murmur.frequency.value = 700; murmur.Q.value = 0.7;
    const lfo = ctx.createOscillator(), lfoG = ctx.createGain(); lfo.frequency.value = 0.08; lfoG.gain.value = 180; lfo.connect(lfoG); lfoG.connect(murmur.frequency); lfo.start();
    const gain = ctx.createGain(); gain.gain.value = 0.05 * roomVol();
    src.connect(lp); lp.connect(murmur); murmur.connect(gain); gain.connect(ctx.destination); src.start();
    const chips = () => {
      if (!roomNodes) return;
      const n = ctx.sampleRate * 0.05, b = ctx.createBuffer(1, n, ctx.sampleRate), d = b.getChannelData(0);
      for (let i = 0; i < n; i++) d[i] = (Math.random() * 2 - 1) * Math.exp(-i / (n * 0.25));
      const s2 = ctx.createBufferSource(); s2.buffer = b; const bp = ctx.createBiquadFilter(); bp.type = 'bandpass'; bp.frequency.value = 2200 + Math.random() * 1500; bp.Q.value = 4;
      const g2 = ctx.createGain(); g2.gain.value = 0.06 * roomVol(); const pn = ctx.createStereoPanner ? ctx.createStereoPanner() : null; if (pn) pn.pan.value = Math.random() * 1.6 - 0.8;
      s2.connect(bp); bp.connect(g2); if (pn) { g2.connect(pn); pn.connect(ctx.destination); } else g2.connect(ctx.destination);
      const burst = 2 + Math.floor(Math.random() * 4); for (let k = 0; k < burst; k++) { const s3 = ctx.createBufferSource(); s3.buffer = b; s3.connect(bp); s3.start(ctx.currentTime + k * 0.07); }
      roomNodes.timer = setTimeout(chips, 6000 + Math.random() * 10000);
    };
    roomNodes = { src, gain, lfo, timer: setTimeout(chips, 4000) };
  }
  function roomStop() { if (!roomNodes) return; clearTimeout(roomNodes.timer); try { roomNodes.src.stop(); roomNodes.lfo.stop(); } catch (e) {} roomNodes = null; }
  function roomSync() { if (opts.roomTone && shown && tab === 'play' && g) { if (roomNodes) roomNodes.gain.gain.value = 0.05 * roomVol(); else roomStart(); } else roomStop(); }
  function atmosphereHtml() {
    const canChat = HAS_TTS() || isGuest();
    if (!canChat && !(window.AudioContext || window.webkitAudioContext)) return '';
    const sel = (key, cur, items) => '<select data-sel="' + key + '">' + items.map(([v, n]) => '<option value="' + v + '"' + (cur === v ? ' selected' : '') + '>' + n + '</option>').join('') + '</select>';
    return '<span class="tr-voice">'
      + (canChat ? '<label title="Players who are out of the hand say the odd line, in their own recorded voice or a stock one — softly, from their side of the table, never over the coaching">🗣 Table chatter ' + sel('talk', talkLevel(), TALK_LEVELS.map(l => [l[0], l[1]])) + '</label>'
        + (talkIdx() > 0 ? sel('chatterVol', opts.chatterVol || 'soft', [['soft', 'soft'], ['normal', 'normal'], ['loud', 'louder']])
          + (isGuest() ? '<label title="Let the host’s table give your character a line now and then (in your recorded voice if you sent one)"><input type="checkbox" data-opt="myTalk"' + (opts.myTalk !== false ? ' checked' : '') + ' /> my character may talk</label>'
            : '<label title="No chatter while you are deciding"><input type="checkbox" data-opt="chatterQuiet"' + (opts.chatterQuiet !== false ? ' checked' : '') + ' /> quiet on my turn</label>'
              + (talkIdx() >= 2 ? (HAS_AI ? '<button class="ghost tr-mini" data-act="ui:freshtalk" title="Throw away the characters’ current lines and have the AI write new ones">🔄 Fresh lines</button>' : '<span class="tr-dim">(add an AI key in ⚙ Settings for lines written per character)</span>') : ''))
          + '<span class="tr-dim" title="' + esc(TALK_LEVELS[talkIdx()][2]) + '">ⓘ</span>' : '') : '')
      + '<label title="A low room murmur and the odd riffle of chips"><input type="checkbox" data-opt="roomTone"' + (opts.roomTone ? ' checked' : '') + ' /> 🎧 Room sound</label>'
      + (opts.roomTone ? sel('roomVol', opts.roomVol || 'soft', [['soft', 'soft'], ['normal', 'normal'], ['loud', 'louder']]) : '') + '</span>';
  }
  const INVITE = code => 'Come and play poker with me on Poker Angel!\nTable code: ' + code + '\n1. Open Poker Angel → 🎓 Trainer (or, on a phone, https://frankthedog.github.io/poker-angel/).\n2. Before you join, press 🎙 My table voice and read the short paragraph — it gives your character your own voice at the table. A phone’s microphone is best.\n3. Type ' + code + ' under Play with friends and press Join a table.';

  const VOICE_SAMPLE = 'This is how I’ll read the coaching. You have Ace King suited on the button. The pot is 9 big blinds and it costs 3 to call, so you need to win 1 time in 4. Raise to 10 big blinds.';
  // What the right-hand column says, minus buttons, drop-downs and stat tables.
  function panelText() {
    const el = $('trPanel'); if (!el) return '';
    const c = el.cloneNode(true);
    c.querySelectorAll('button, details, .tr-detail, .tr-speak, input, select, .tr-optlist, .tr-nosay').forEach(x => x.remove());
    // a pause after each heading and block, and at each line break, so sentences don't run together
    c.querySelectorAll('div, b:not(.tr-lbl), br').forEach(x => x.after('. '));
    return c.textContent.replace(/\n+/g, '. ');
  }
  // Read only what's new. The column is re-drawn on every move and often keeps earlier text (your last
  // explanation stays while the advice appears; each bot move adds a line), so the reader remembers,
  // sentence by sentence, what it has already said in this hand / lesson step / replay and skips it.
  const sentencesOf = t => t.split(/(?<=[.!?:])\s+/).map(x => x.trim()).filter(Boolean);
  let saidKey = '', said = new Set();
  const sayContext = () => tab + '|' + (g ? handKey() : '') + '|' + (drill.ex ? drill.ex.id + '.' + drill.ex.si : '') + '|' + (drill.replay ? drill.replay.rec.id : '');
  function markSaid(t) { const key = sayContext(); if (key !== saidKey) { saidKey = key; said = new Set(); } sentencesOf(t).forEach(x => said.add(x)); }
  function autoSpeak(text) {
    if (!opts.speak || !CAN_SPEAK || (sleepAudio && !sleepAudio.paused)) return;
    clearTimeout(speakTimer);
    speakTimer = setTimeout(() => {
      if (text != null) {                                         // a drill answer: read it once
        const t = forSpeech(text);
        if (!t || t === spokenLast) return;
        spokenLast = t; speak(t); return;
      }
      const key = sayContext(); if (key !== saidKey) { saidKey = key; said = new Set(); }
      const fresh = sentencesOf(forSpeech(panelText())).filter(x => !said.has(x));
      if (!fresh.length) return;
      fresh.forEach(x => said.add(x));
      speak(fresh.join(' '));
    }, 180);
  }
  // What to read beside the table (explanation, advice, lesson notes) goes in the right-hand column.
  // The right-hand column scrolls as one; a NEW explanation brings it back to the top so it's seen.
  let panelLast = '';
  function setPanel(html) {
    const el = $('trPanel'); if (!el) return;
    if (html && html !== panelLast && $('trSide')) $('trSide').scrollTop = 0;
    panelLast = html || '';
    el.innerHTML = html ? (CAN_TALK() ? '<div class="tr-row tr-speak"><button class="' + (opts.speak ? 'primary' : 'ghost') + ' tr-mini" data-act="ui:speaktoggle" title="Read each new explanation aloud, hand after hand, until you switch it off">' + (opts.speak ? '🔊 Read aloud: on' : '🔇 Read aloud: off') + '</button>'
      + '<button class="ghost tr-mini" data-act="ui:speak">↻ Read again</button><button class="ghost tr-mini" data-act="ui:hush" title="Stop this explanation — reading stays on for the next one">⏹ Stop</button></div>' : '') + html : '';
    if (html) autoSpeak();
  }
  function feltHtml() {
    const pot = potTotal(g), betting = g.players.reduce((a, p) => a + p.bet, 0);
    let felt = '';
    for (let i = 0; i < g.players.length; i++) felt += seatHtml(i);
    for (let i = 0; i < g.players.length; i++) felt += seatNote(i);
    g.players.forEach((p, i) => { if (p.bet > 0 && !g.over) { const b = layout().bet[view(i)]; felt += '<div class="tr-bet" style="left:' + b[0] + '%;top:' + b[1] + '%">' + bbs(p.bet) + '</div>'; } });
    const dl = layout().deal[view(g.button)];
    felt += '<div class="tr-dealer" style="left:' + dl[0] + '%;top:' + dl[1] + '%">D</div>';
    felt += '<div class="tr-pot">Pot ' + bbs(r2(pot)) + (betting && !g.over && pot - betting > 0 ? ' <small>(' + bbs(r2(pot - betting)) + ' in the middle)</small>' : '') + '</div>';
    let board = ''; for (let k = 0; k < 5; k++) board += g.board[k] ? cardHtml(g.board[k], 'lg') : '<span class="tc lg slot"></span>';
    return felt + '<div class="tr-board">' + board + '</div>';
  }
  function roomBar() {
    if (!room) return '';
    const names = (isHost() ? tablePlayers() : room.players || []).map(p => esc(p.name)).join(' · ');
    const mode = isHost()
      ? '<label title="Face up: everyone sees every card and every grade as it happens. Own only: your own cards and grades; everyone’s are revealed when the hand ends."><input type="checkbox" data-room="faceUp"' + (room.faceUp ? ' checked' : '') + ' /> Cards face up for everyone</label>'
      : '<span class="tr-dim">' + (room.faceUp ? 'Cards face up for everyone' : 'Own cards only — all revealed at the end of each hand') + '</span>';
    return '<div class="tr-room"><b>👥 Table ' + esc(room.code) + '</b>'
      + (isHost() ? '<button class="ghost" data-act="room:copy">Copy code</button><button class="ghost" data-act="room:invite" title="A message to send your friends: the code, and how to join — with their table voice">📋 Copy invitation</button>' : '')
      + '<span class="tr-dim">' + (room.status ? esc(room.status) : names) + '</span><span style="flex:1"></span>' + mode
      + '<button class="ghost" data-act="room:leave">' + (isHost() ? 'Close table' : 'Leave') + '</button></div>';
  }
  // Tournament settings, remembered between games.
  function fieldHtml() {
    return '<label class="tr-dim tr-field">Opponents <select id="trField" style="width:auto">' + Object.keys(FIELDS).map(k => '<option value="' + k + '"' + ((opts.field || 'mixed') === k ? ' selected' : '') + '>' + FIELDS[k].name + '</option>').join('') + '</select></label>'
      + '<label class="tr-dim tr-field" title="Everyone starts each cash hand with this stack. Under 40 big blinds the grading tightens; at 20 or fewer it is push/fold.">Stacks <select id="trDepth" style="width:auto">' + [[100, '100 big blinds (deep)'], [60, '60 big blinds'], [40, '40 big blinds'], [25, '25 big blinds (short)'], [15, '15 big blinds (push/fold)']].map(([v, n]) => '<option value="' + v + '"' + ((opts.depth || 100) === v ? ' selected' : '') + '>' + n + '</option>').join('') + '</select></label>';
  }
  function tourOptsHtml() {
    const t = opts.tour || {}, sel = (id, cur, list) => '<select id="' + id + '" style="width:auto">' + list.map(o => '<option value="' + o[0] + '"' + (String(o[0]) === String(cur) ? ' selected' : '') + '>' + o[1] + '</option>').join('') + '</select>';
    return '<div class="tr-row">'
      + '<label class="tr-dim">Starting stack ' + sel('trTStart', t.startBB || 40, [[25, '25 big blinds (short)'], [40, '40 big blinds (turbo)'], [75, '75 big blinds (a standard online sit-and-go)'], [100, '100 big blinds (deep)']]) + '</label>'
      + '<label class="tr-dim">Blinds rise every ' + sel('trTSpeed', t.perLevel || 6, [[4, '4 hands'], [6, '6 hands'], [9, '9 hands'], [12, '12 hands']]) + '</label>'
      + '<label class="tr-dim">Prizes ' + sel('trTPay', t.payouts || 'top3', Object.keys(PAYOUTS).map(k => [k, PAYOUTS[k].name])) + '</label></div>';
  }
  function tourBar() {
    const T = g && g.tour; if (!T) return '';
    const icm = tourIcm(g), mine = me >= 0 ? icm[me] : null;
    return '<div class="tr-tour"><b>🏆 ' + (T.done ? 'Tournament over' : esc(tourLine(g))) + '</b>'
      + (mine != null && !T.done ? '<span>Your prize equity <b>' + usd(mine) + '</b> of $' + T.pool + '</span>' : '') + '</div>';
  }
  function renderPlay() {
    const m = $('trMain');
    setPanel('');
    if (!g) {
      if (room) {
        m.innerHTML = roomBar() + '<div class="tr-drill"><div class="tr-q">' + (isHost()
          ? (room.status ? esc(room.status) : 'Your table code is <b class="tr-code">' + esc(room.code) + '</b><br>Send it to your friends. ' + (IN_BROWSER ? 'They open this same page, type it under <b>Play with friends</b> and press <b>Join a table</b>.' : 'In Poker Angel they open 🎓 Trainer → <b>Join a table</b> and type it in.') + ' Empty seats are played by bots.')
          : (room.status ? esc(room.status) : 'Joined table <b>' + esc(room.code) + '</b>. Waiting for the host to start…')) + '</div>'
          + (isHost() && !room.status ? '<div class="tr-row">' + fieldHtml() + '</div><div class="tr-row"><button data-act="play:next">🃏 Deal cash hands (100bb)</button></div>'
            + '<div class="tr-q" style="margin-top:6px"><b>…or a tournament</b> for the whole table:</div>' + tourOptsHtml() + '<div class="tr-row"><button data-act="tour:start">🏆 Start a tournament</button></div>' : '') + '</div>';
        renderSpot(); return;
      }
      m.innerHTML = '<div class="tr-drill">' + dailyHtml() + '<div class="tr-q tr-levelbox">' + levelSelHtml() + '<br><span class="tr-dim">' + esc(COACH_LEVELS[lvlIdx()][2]) + ' Change it any time — it changes how things are explained, not the advice.</span></div>'
        + '<div class="tr-q"><b>Play 8-handed No-Limit Hold’em.</b><br>Blinds 0.5/1, everyone 100bb deep every hand. Bots play real styles — tight, loose, passive, a calling station, a maniac — and their style is on their seat, so you can practise adjusting to it.<br><br>Every decision is graded on the right as it’s made: preflop against the charts, after the flop on equity against what each opponent’s actions say they hold, and the pot odds. When it’s your turn, the right-hand column sums up the hand so far and says what to do, with the size; when a hand ends the AI coach can talk you through it.</div>'
        + '<div class="tr-row">' + fieldHtml() + '</div>'
        + '<div class="tr-row"><button data-act="play:next">🃏 Play cash hands against the bots</button>' + AUTO_BTN + '</div>'
        + '<div class="tr-q" style="margin-top:4px">🎬 <b>Watch the Angel play</b> — sit back while the Angel plays hand after hand in your seat: every card face up, every move (its own and the bots’) explained beside the player and in the column on the right, with the bet sizes and the strategy behind them' + (CAN_SPEAK ? ', read aloud as it goes' : '') + '. Press Stop whenever you want the seat back.</div>'
        + '<div class="tr-row">' + autoOptsHtml() + '</div>'
        + '<div class="tr-q tr-sleep" style="margin-top:8px">🌙 <b>Sleep story</b> — the Angel plays a quiet table in a calm, unhurried voice, explaining every hand, and closes softly when the time is up. Lights off, press one:'
        + '<div class="tr-row">' + [20, 30, 45, 60].map(m => '<button class="ghost" data-act="play:sleep" data-v="' + m + '">🌙 ' + m + ' minutes</button>').join('') + '</div></div>'
        + '<div class="tr-q" style="margin-top:8px"><b>🏆 Tournament</b> — a sit-and-go against the bots: blinds rise, the big blind posts an ante (as at the WSOP), players are knocked out and the top places are paid. Once stacks are short, every shove, fold and call is graded in prize money (ICM) next to the chip-only answer.</div>'
        + tourOptsHtml() + '<div class="tr-row"><button data-act="tour:start">🏆 Start a tournament</button></div>'
        + '<div class="tr-q" style="margin-top:8px"><b>Play with friends</b> — over the internet, everyone graded, everyone learning together. ' + (IN_BROWSER ? 'Friends open this same page — nothing to install.' : 'Each friend needs Poker Angel.') + '</div>'
        + '<div class="tr-row"><input id="trName" placeholder="Your name" maxlength="16" style="width:180px" value="' + esc(ls(NAME_KEY) || '') + '" />'
        + '<button data-act="room:host">👥 Host a table</button>'
        + '<input id="trCode" placeholder="Table code" maxlength="5" style="width:130px;text-transform:uppercase" /><input id="trPw" placeholder="Password (optional)" maxlength="24" style="width:150px" /><button class="ghost" data-act="room:join">🔗 Join a table</button></div>'
        + '<div class="tr-dim"><label style="display:inline-flex;gap:6px;align-items:center"><input type="checkbox" data-opt="faceUp"' + (opts.faceUp ? ' checked' : '') + ' /> Cards face up for everyone at my table (a teaching table; otherwise each player sees only their own)</label> · a password keeps strangers out even if they guess the code.</div>' + voiceRecHtml() + '</div>';
      renderSpot(); return;
    }
    const T = g.tour, felt = feltHtml();
    let actions;
    const extras = (HAS_AI ? '<button class="ghost" data-act="play:ai">🤖 Ask the AI coach about this hand</button>' : '') + '<button class="ghost" data-act="play:copy">📋 Copy hand history</button>';
    const pend = pauseOn() && !autoOn() && !autoClose ? myPending() : null;
    const panel = pend ? '<div class="tr-explain">' + decHtml(pend, true)
      + (g.over ? '' : '<div class="tr-row">' + (holding() ? '<span class="tr-dim">Press Continue ▶ under the table when you’re ready.</span>' : '<button class="ghost" data-act="play:continue">Got it</button>') + '</div>') + '</div>' : '';
    if (autoOn()) {
      actions = autoBar();
    } else if (g.over && T && T.done) {
      actions = (isGuest() ? '<span class="tr-wait">Waiting for the host to start the next game…</span>' : '<button class="primary" data-act="tour:again">🏆 New tournament</button><button class="ghost" data-act="tour:menu">Back to the menu</button>') + extras;
    } else if (g.over) {
      actions = (isGuest() ? '<span class="tr-wait">Waiting for the host to deal the next hand…</span>' : '<button class="primary" data-act="play:next">Next hand ▶</button>') + extras + (room ? '' : AUTO_BTN);
    } else if (holding()) {
      actions = '<button class="primary" data-act="play:continue">Continue ▶</button><span class="tr-dim">Read the explanation on the right first — the bots wait for you.</span>';
    } else if (watching()) {
      actions = '<button class="primary" data-act="play:wnext">Next move ▶</button><button class="ghost" data-act="play:wall">Play the hand out ▶▶</button><span class="tr-dim">You folded — ' + esc(g.players[g.toAct].name) + ' is next to act. Each player’s reason appears in a box beside them.</span>';
    } else if (stepBots()) {
      actions = '<button class="primary" data-act="play:wnext">Next move ▶</button><button class="ghost" data-act="play:wall">Skip to my turn ▶▶</button><span class="tr-dim">' + esc(g.players[g.toAct].name) + ' is next to act. Read the box beside each player, then press Next move.</span>';
    } else if (me < 0) actions = '<span class="tr-wait">Watching — you’re dealt in from the next ' + (T ? 'game' : 'hand') + '.</span>';
    else if (T && g.players[me].out) actions = '<span class="tr-wait">You’re out in ' + ordinal(T.place[me]) + ' — the rest plays on.</span>' + (isGuest() ? '' : '<button class="ghost" data-act="tour:menu">Leave this tournament</button>');
    else if (g.toAct !== me) actions = '<span class="tr-wait">' + (g.toAct >= 0 ? esc(g.players[g.toAct].name) + ' is thinking…' : 'Sending…') + '</span>';
    else if (room && room.web && room.sent === handKey() + '/' + g.acts.length) actions = '<span class="tr-wait">Sending your move to the table…</span>';
    else {
      const L = legal(g, me), b = ['<button class="fold" data-act="play:fold">Fold</button>'];
      b.push(L.toCall > 0 ? '<button data-act="play:call">Call ' + bbs(L.toCall) + (L.toCall >= g.players[me].stack ? ' (all-in)' : '') + '</button>' : '<button data-act="play:check">Check</button>');
      if (L.canRaise) {
        sizes().forEach(z => b.push('<button class="raise" data-act="play:raise" data-to="' + z.to + '">' + esc(z.label) + '</button>'));
        b.push('<span class="tr-custom"><input type="number" id="trTo" min="' + L.minTo + '" max="' + L.maxTo + '" step="0.5" value="' + L.minTo + '" /><button class="raise" data-act="play:raiseTo">' + (g.curBet > 0 ? 'Raise to' : 'Bet') + '</button></span>');
      }
      b.push('<button class="ghost" data-act="play:hint">💡 Hint</button>');
      if (!room) b.push(AUTO_BTN);
      actions = b.join('');
    }
    const optsRow = levelSelHtml() + '<label><input type="checkbox" data-opt="advise"' + (opts.advise ? ' checked' : '') + ' /> Advise me before I act</label>'
      + '<label><input type="checkbox" data-opt="detail"' + (opts.detail ? ' checked' : '') + ' /> 📊 Detailed explanations (stat tables)</label>'
      + (CAN_TALK() ? '<label><input type="checkbox" data-opt="speak"' + (opts.speak ? ' checked' : '') + ' /> 🔊 Read explanations aloud</label>' + voiceSelHtml() : '') + atmosphereHtml()
      + '<label><input type="checkbox" data-opt="pause"' + (pauseOn() ? ' checked' : '') + ' /> Explain after I act' + (room ? '' : ' (and pause)') + '</label>'
      + (room ? '' : '<label><input type="checkbox" data-opt="showBots"' + (opts.showBots ? ' checked' : '') + ' /> Show the bots’ cards</label>')
      + (room ? '' : '<label title="Each bot move waits for Next move ▶, so you can read the comment beside the player. Untick to let the bots play at normal speed."><input type="checkbox" data-opt="stepBots"' + (opts.stepBots !== false ? ' checked' : '') + ' /> ⏯ Bots wait for Next</label>')
      + (room ? '' : '<label title="When you fold, the hand carries on one move at a time with the bots’ cards face up and each move explained."><input type="checkbox" data-opt="watch"' + (opts.watch !== false ? ' checked' : '') + ' /> 👀 Watch the bots after I fold</label>')
      + (room || T ? '' : '<label title="Like PokerStars Zoom: when you fold, the rest of the hand plays out at once and you’re dealt the next one — many more hands per hour."><input type="checkbox" data-opt="fastFold"' + (opts.fastFold ? ' checked' : '') + ' /> ⚡ Fast-fold</label>');
    const myTurn = !holding() && !autoOn() && !g.over && me >= 0 && g.toAct === me;
    const advice = myTurn ? storyHtml() + (opts.advise ? adviceHtml() : '') : '';
    m.innerHTML = roomBar() + tourBar() + ratingsBar() + '<div class="tr-felt-wrap"><div class="tr-felt">' + felt + '</div></div>'
      + '<div class="tr-actions">' + actions + '</div>'
      + '<div class="tr-key">Key: ' + Array.from(new Set(g.players.map((q, j) => posOf(g, j)).filter(Boolean))).map(p => '<b>' + p + '</b> ' + POS_FULL[p] + (p === 'BTN' ? ' (the dealer)' : p === 'UTG' ? ' (first to act)' : '')).join(' · ') + ' · <b>bb</b> big blinds · <b>D</b> dealer button · keys: <b>F</b> fold <b>C</b> call/check <b>R</b> raise <b>H</b> ½ pot <b>P</b> pot <b>N</b> next</div>'
      + '<div class="tr-opts">' + optsRow + '<span>Hand #' + g.handNo + (T ? '' : ' · your session ' + (stats.net >= 0 ? '+' : '') + bbs(stats.net)) + '</span></div>';
    setPanel(primerHtml() + (autoOn() ? autoHtml() : autoClose) + (autoClose ? '' : watchHtml()) + panel + advice);
    renderSpot();
  }
  function renderSpot() {
    const el = $('trSpot'); if (!el) return;
    if (tab !== 'play' || !g) { el.innerHTML = '<b>Coach</b><br>' + (tab === 'play' ? (room ? 'Grades for the whole table appear below.' : 'Deal a hand to start.') : 'Answers and explanations appear below.'); return; }
    const T = g.tour, lines = [];
    if (T) {
      const icm = tourIcm(g);
      lines.push('<b>🏆 ' + esc(tourLine(g)) + '</b>');
      g.players.forEach((q, j) => { if (T.chips[j] > 0) lines.push('· ' + esc(j === me ? 'You' : q.name) + ': ' + r1(T.chips[j] / T.levels[T.level]) + 'bb → ' + usd(icm[j])); });
      lines.push('<span class="tr-dim">Prize equity = what each stack is worth in prize money right now (ICM).</span>');
    }
    if (me < 0 || !g.players[me] || !g.players[me].cards || !g.players[me].cards.length) { el.innerHTML = lines.concat(['<b>Hand #' + g.handNo + '</b>', 'Watching.']).join('<br>'); return; }
    // your hand, its strength and the price are in the box above your cards; each opponent's read is in
    // the box beside them as they act. Only what isn't on the table stays here.
    if (!g.over && g.toAct === me) {
      const sp = shortSpot(g, me);
      if (sp) lines.push('<span class="tr-dim">' + (sp.type === 'shove' ? 'Push/fold spot: ' + r1(sp.S) + 'bb effective, ' + sp.m + ' behind.' : 'Facing an all-in of ' + r1(sp.S) + 'bb.') + '</span>');
    }
    el.innerHTML = plain(lines.join('<br>'));
  }
  // A new game at the table: everyone at a friends' table is seated afresh.
  function freshTable() { g = null; decisions = []; token++; if (isHost()) for (const c of room.conns.values()) c.pending = true; }
  function startTournament() {
    if (isGuest()) return;
    const o = { startBB: +(($('trTStart') || {}).value || (opts.tour && opts.tour.startBB) || 40), perLevel: +(($('trTSpeed') || {}).value || (opts.tour && opts.tour.perLevel) || 6),
      payouts: ($('trTPay') || {}).value || (opts.tour && opts.tour.payouts) || 'top3' };
    opts.tour = o; saveOpts();
    freshTable();
    g = newGame(Math.random, opts.field); g.players[0].name = room ? myName() : 'You';
    newTournament(g, o);
    startHand();
  }

  // ---- drills ----
  const rnd = n => Math.floor(Math.random() * n);
  const pickOf = arr => arr[rnd(arr.length)];
  function resHtml(G, extra) { autoSpeak(plain(G.head) + '. ' + plain(G.why)); return '<div class="tr-res"><b>' + esc(plain(G.head)) + '</b>\n' + fmtWhy(G.why) + (extra || '') + '</div>'; }
  function score(key, good) { const a = stats.drills[key]; a[0]++; if (good) a[1]++; saveStats(); if (key === 'pre' || key === 'pf') dailyAdd(key); }

  function genPre() {
    let pos, raises = 0, openerPos = '';
    if (Math.random() < 0.5) pos = pickOf(['UTG', 'UTG+1', 'LJ', 'HJ', 'CO', 'BTN', 'SB']);
    else {
      pos = pickOf(['UTG+1', 'LJ', 'HJ', 'CO', 'BTN', 'SB', 'BB']); raises = 1;
      const order = ['UTG', 'UTG+1', 'LJ', 'HJ', 'CO', 'BTN', 'SB'], at = order.indexOf(pos);
      openerPos = pickOf(order.slice(0, at < 0 ? order.length : at));
    }
    const c = combos()[rnd(Math.random() < 0.6 ? 700 : 1326)];   // lean toward hands near the edges of the ranges
    const cards = [c.x, c.y].sort((a, b) => b.r - a.r);
    drill.pre = { street: 0, pos, raises, openerPos, heroOpened: false, facingAllIn: false, cards, k: cls(c.x, c.y), done: null };
  }
  function renderPre() {
    if (!drill.pre) genPre();
    const d = drill.pre;
    const q = plain(d.raises === 0 ? 'Everyone has folded to you. You are in the <b>' + d.pos + '</b>.' : 'The <b>' + d.openerPos + '</b> raises to 2.5bb. Everyone else folds to you in the <b>' + d.pos + '</b>.');
    const btns = d.raises === 0 ? [['fold', 'Fold'], ['call', 'Limp'], ['raise', 'Raise to ' + (d.pos === 'SB' ? 3 : 2.5) + 'bb']] : [['fold', 'Fold'], ['call', 'Call'], ['raise', '3-bet']];
    let h = '<div class="tr-drill"><div class="tr-q">Before the flop · 8 players · everyone has 100 big blinds. ' + q + ' What do you do?</div>'
      + '<div class="tr-hand">' + d.cards.map(c => cardHtml(c, 'lg')).join('') + '<span class="tr-dim">' + esc(handWords(d.k)) + ' (' + d.k + ')</span></div>';
    if (!d.done) h += '<div class="tr-row">' + btns.map(b => '<button' + (b[0] === 'fold' ? ' class="fold"' : '') + ' data-act="pre:' + b[0] + '">' + b[1] + '</button>').join('') + '</div>';
    else {
      const A = preflopAdvice(d.k, d);
      h += resHtml(d.done) + (A.view ? '<div class="tr-dim">Chart: ' + esc((VIEWS.find(v => v.id === A.view) || {}).name || '') + ' — your hand is outlined.</div>' + gridHtml(A.view, d.k) + legendHtml(A.view) : '')
        + '<div class="tr-row"><button data-act="pre:next">Next hand ▶</button></div>';
    }
    $('trMain').innerHTML = h + drillScore('pre', 'correct') + '</div>';
  }
  function answerPre(kind) {
    const d = drill.pre; if (!d || d.done) return;
    d.done = gradePre(d, kind); score('pre', d.done.v !== 'bad');
    feed('', '<b>Preflop drill · ' + esc(d.done.head) + '</b>' + fmtWhy(d.done.why));
    renderPre();
  }

  function genOdds() {
    const P = pickOf([4, 6, 7.5, 9, 10, 12, 15, 18, 20, 25, 30, 40, 50, 60]);
    const f = pickOf([0.25, 0.33, 0.5, 0.66, 0.75, 1, 1.25, 1.5, 2]);
    drill.odds = { P, B: Math.max(1, half(P * f)), done: null };
  }
  function renderOdds() {
    if (!drill.odds) genOdds();
    const d = drill.odds, need = d.B / (d.P + 2 * d.B) * 100;
    let h = '<div class="tr-drill"><div class="tr-q">The pot is <b>' + bbs(d.P) + '</b>. Your opponent bets <b>' + bbs(d.B) + '</b>.<br>What equity do you need to call? (in %)</div>';
    if (!d.done) h += '<div class="tr-row"><input type="number" id="trOddsIn" min="0" max="100" step="0.1" placeholder="%" /><button data-act="odds:check">Check</button></div>';
    else h += d.done + '<div class="tr-row"><button data-act="odds:next">Next ▶</button></div>';
    h += '<div class="tr-dim">Formula: call ÷ (pot + bet + call). Common sizes: ⅓ pot → 20% · ½ → 25% · ⅔ → 28.4% · ¾ → 30% · pot → 33.3% · 2× pot → 40%. Equity from outs: about outs × 2 for one card, outs × 4 for two.</div>';
    $('trMain').innerHTML = h + drillScore('odds', 'within 2 points') + '</div>';
    void need;
  }
  function answerOdds() {
    const d = drill.odds; if (!d || d.done) return;
    const v = parseFloat(($('trOddsIn') || {}).value);
    if (!isFinite(v)) { toast('Type a percentage', 'red'); return; }
    const need = d.B / (d.P + 2 * d.B) * 100, err = Math.abs(v - need), ok = err <= 2;
    score('odds', ok);
    const G = V(ok ? 'good' : err <= 5 ? 'ok' : 'bad', 'The answer: ' + r1(need) + '%' + (ok ? ' — you had it' : ''),
      'You call ' + bbs(d.B) + ' to win the ' + bbs(d.P + d.B) + ' already in the middle, so the final pot is ' + bbs(d.P + 2 * d.B) + '.\n'
      + bbs(d.B) + ' ÷ ' + bbs(d.P + 2 * d.B) + ' = ' + r1(need) + '%. As odds: ' + r1((d.P + d.B) / d.B) + ' to 1. You said ' + v + '%.', 0);
    d.done = resHtml(G);
    renderOdds();
  }

  const EQ_RANGES = [[1, 'any two cards'], [0.5, 'the top 50% of hands'], [0.25, 'the top 25%'], [0.12, 'the top 12%'], [0.05, 'the top 5% (premiums)']];
  function genEq() {
    const deck = shuffled(Math.random), n = pickOf([0, 3, 3, 3, 4]);
    const cards = [deck.pop(), deck.pop()], board = []; for (let k = 0; k < n; k++) board.push(deck.pop());
    const r = pickOf(EQ_RANGES);
    drill.eq = { cards, board, w: r[0], label: r[1], done: null };
  }
  function renderEq() {
    if (!drill.eq) genEq();
    const d = drill.eq;
    let h = '<div class="tr-drill"><div class="tr-q">You hold this hand' + (d.board.length ? ' on this board' : ' preflop') + '. Your one opponent holds <b>' + d.label + '</b>. Estimate your equity (your share of the pot if all the cards were dealt out).</div>'
      + '<div class="tr-hand">' + d.cards.map(c => cardHtml(c, 'lg')).join('') + (d.board.length ? '<span class="tr-sep"></span>' + d.board.map(c => cardHtml(c, 'lg')).join('') : '') + '</div>';
    if (!d.done) h += '<div class="tr-row"><input type="range" id="trEqSl" min="0" max="100" value="50" /><input type="number" id="trEqIn" min="0" max="100" value="50" />%<button data-act="eq:check">Check</button></div>';
    else h += d.done + '<div class="tr-row"><button data-act="eq:next">Next ▶</button></div>';
    $('trMain').innerHTML = h + drillScore('eq', '') + '</div>';
    const sl = $('trEqSl'), inp = $('trEqIn');
    if (sl && inp) { sl.oninput = () => { inp.value = sl.value; }; inp.oninput = () => { sl.value = inp.value; }; }
  }
  function answerEq() {
    const d = drill.eq; if (!d || d.done) return;
    const v = parseFloat(($('trEqIn') || {}).value);
    if (!isFinite(v)) { toast('Type a percentage', 'red'); return; }
    const truth = equityVsRanges(d.cards, d.board, [{ width: d.w, post: [] }], 6000);
    const err = Math.abs(v - truth);
    const a = stats.drills.eq; a[0]++; if (err <= 5) a[1]++; a[2] = Math.round((a[2] + err) * 10) / 10; saveStats();
    let made = '';
    if (d.board.length) {
      const dr = draws(d.cards, d.board), bits = [handName(evalHand(d.cards.concat(d.board)))];
      if (dr.flush) bits.push('flush draw'); if (dr.straight) bits.push('straight draw');
      made = '\nYou have: ' + bits.join(' + ') + '.';
    }
    const G = V(err <= 5 ? 'good' : err <= 10 ? 'ok' : 'bad', 'Your equity is ' + truth + '% (you said ' + v + '%, off by ' + r1(err) + ')',
      'Against ' + d.label + ', simulated 6,000 times.' + made, 0);
    d.done = resHtml(G);
    renderEq();
  }

  function genOuts() {
    for (let t = 0; t < 500; t++) {
      const deck = shuffled(Math.random), h = [deck.pop(), deck.pop()], v = [deck.pop(), deck.pop()], n = Math.random() < 0.6 ? 3 : 4, b = [];
      for (let k = 0; k < n; k++) b.push(deck.pop());
      if (evalHand(h.concat(b)) >= evalHand(v.concat(b))) continue;
      const outs = deck.filter(c => evalHand(h.concat(b, [c])) > evalHand(v.concat(b, [c])));
      if (outs.length >= 2 && outs.length <= 20) { drill.outs = { h, v, b, outs, left: deck.length, done: null }; return; }
    }
  }
  function renderOuts() {
    if (!drill.outs) genOuts();
    const d = drill.outs;
    let h = '<div class="tr-drill"><div class="tr-q">You are behind. Both hands are face up. How many cards on the <b>' + (d.b.length === 3 ? 'turn' : 'river') + '</b> put you ahead?</div>'
      + '<div class="tr-hand"><span class="tr-dim">You</span>' + d.h.map(c => cardHtml(c, 'lg')).join('') + '<span class="tr-sep"></span><span class="tr-dim">Them</span>' + d.v.map(c => cardHtml(c, 'lg')).join('') + '</div>'
      + '<div class="tr-hand"><span class="tr-dim">Board</span>' + d.b.map(c => cardHtml(c, 'lg')).join('') + '</div>';
    if (!d.done) h += '<div class="tr-row"><input type="number" id="trOutsIn" min="0" max="45" placeholder="outs" /><button data-act="outs:check">Check</button></div>';
    else h += d.done + '<div class="tr-hand">' + d.outs.slice().sort((a, b) => b.r - a.r || a.s - b.s).map(c => cardHtml(c)).join('') + '</div><div class="tr-row"><button data-act="outs:next">Next ▶</button></div>';
    $('trMain').innerHTML = h + drillScore('outs', 'exact') + '</div>';
  }
  function answerOuts() {
    const d = drill.outs; if (!d || d.done) return;
    const v = parseInt(($('trOutsIn') || {}).value, 10);
    if (!isFinite(v)) { toast('Type a number', 'red'); return; }
    const n = d.outs.length, ok = v === n; score('outs', ok);
    const next = r1(n / d.left * 100);
    let two = '';
    if (d.b.length === 3) { const L = d.left; two = '\nOver turn AND river it is about ' + r1((1 - (L - n) * (L - n - 1) / (L * (L - 1))) * 100) + '% (rule of 4: ≈' + (n * 4) + '%), counting only these outs.'; }
    const G = V(ok ? 'good' : Math.abs(v - n) <= 1 ? 'ok' : 'bad', 'The answer: ' + n + ' outs' + (ok ? ' — you had it' : ' (you said ' + v + ')'),
      n + ' of the ' + d.left + ' unseen cards win it: ' + next + '% on the next card (rule of 2: ≈' + (n * 2) + '%).' + two
      + '\nYou now: ' + handName(evalHand(d.h.concat(d.b))) + ' · them: ' + handName(evalHand(d.v.concat(d.b))) + '.', 0);
    d.done = resHtml(G);
    renderOuts();
  }

  function genSd() {
    const deck = shuffled(Math.random), board = [];
    const hands = [0, 1, 2].map(() => [deck.pop(), deck.pop()]);
    for (let k = 0; k < 5; k++) board.push(deck.pop());
    drill.sd = { board, hands, scores: hands.map(h => evalHand(h.concat(board))), done: null };
  }
  function renderSd() {
    if (!drill.sd) genSd();
    const d = drill.sd, best = Math.max.apply(null, d.scores);
    let h = '<div class="tr-drill"><div class="tr-q">Showdown. Which hand wins?</div>'
      + '<div class="tr-hand"><span class="tr-dim">Board</span>' + d.board.map(c => cardHtml(c, 'lg')).join('') + '</div><div class="tr-sd">';
    d.hands.forEach((hd, i) => {
      h += '<button class="ghost' + (d.done && d.scores[i] === best ? ' tr-win' : '') + '" data-act="sd:' + i + '"' + (d.done ? ' disabled' : '') + '><span class="tr-hand">' + hd.map(c => cardHtml(c)).join('') + '</span>'
        + (d.done ? '<small>' + esc(handName(d.scores[i])) + '</small>' : '<small>Player ' + (i + 1) + '</small>') + '</button>';
    });
    h += '<button class="ghost" data-act="sd:split"' + (d.done ? ' disabled' : '') + '>Split pot</button></div>';
    if (d.done) h += d.done + '<div class="tr-row"><button data-act="sd:next">Next ▶</button></div>';
    $('trMain').innerHTML = h + drillScore('sd', 'correct') + '</div>';
  }
  function answerSd(v) {
    const d = drill.sd; if (!d || d.done) return;
    const best = Math.max.apply(null, d.scores), ws = d.scores.map((s, i) => s === best ? i : -1).filter(i => i >= 0);
    const ok = v === 'split' ? ws.length > 1 : (ws.length === 1 && ws[0] === +v);
    score('sd', ok);
    const G = V(ok ? 'good' : 'bad', ws.length > 1 ? 'The pot is split' : 'Player ' + (ws[0] + 1) + ' wins',
      (ws.length > 1 ? 'Split pot between players ' + ws.map(i => i + 1).join(' and ') : 'Player ' + (ws[0] + 1) + ' wins') + ' with ' + handName(best)
      + '. Each player makes the best five cards from their two and the five on the board — kickers decide ties within the same hand.', 0);
    d.done = resHtml(G);
    renderSd();
  }

  // ---- push/fold drill (the equilibrium tables) ----
  // 8-handed, big-blind ante. The pusher's position is set by how many players are behind them (m).
  const PF_POS = ['UTG', 'UTG+1', 'LJ', 'HJ', 'CO', 'BTN', 'SB', 'BB'];
  const pusherPos = m => PF_POS[7 - m];
  const callerPos = (m, j) => PF_POS[7 - m + j];
  const pfNeed = (m, j, S) => { const bp = m === 1 ? 0.5 : 0, bj = j === m ? 1 : (j === m - 1 && m >= 2 ? 0.5 : 0); return (S - bj) / (2 * S + 2.5 - bp - bj); };
  function pickNearEdge(test) {   // half the time, a hand whose answer changes within a few bb of this depth
    const all = PK_HAND_ORDER, near = all.filter(test);
    return (near.length && Math.random() < 0.55) ? pickOf(near) : pickOf(all);
  }
  function classCards(k) { const c = PushFold.combosOfClass(k)[rnd(PushFold.combosOfClass(k).length)]; return [fromId(c[0]), fromId(c[1])].sort((a, b) => b.r - a.r); }
  function genPf() {
    const m = 1 + rnd(7), S = pickOf([3, 4, 5, 6, 7, 8, 8, 9, 10, 10, 11, 12, 12, 13, 14, 15, 16, 18, 20]);
    if (Math.random() < 0.6) {
      const k = pickNearEdge(c => Math.abs(PushFold.maxPush(c, m) - S) <= 3 && PushFold.maxPush(c, m) > 0);
      drill.pf = { type: 'push', m, S, k, cards: classCards(k), done: null };
    } else {
      const j = 1 + rnd(m), k = pickNearEdge(c => Math.abs(PushFold.maxCall(c, m, j) - S) <= 3 && PushFold.maxCall(c, m, j) > 0);
      drill.pf = { type: 'call', m, j, S, k, cards: classCards(k), done: null };
    }
  }
  function pfGrid(kind, m, j, me) {
    let h = '<div class="tr-grid tr-pfgrid">';
    for (let i = 12; i >= 0; i--) for (let jj = 12; jj >= 0; jj--) {
      const a = RK[i], b = RK[jj], k = i === jj ? a + a : i > jj ? a + b + 's' : b + a + 'o';
      const n = kind === 'push' ? PushFold.maxPush(k, m) : PushFold.maxCall(k, m, j);
      const shade = n >= 20 ? 'p4' : n >= 13 ? 'p3' : n >= 8 ? 'p2' : n >= 1 ? 'p1' : '';
      h += '<span class="' + shade + (k === me ? ' me' : '') + '" title="' + k + ': ' + (n ? (n >= 20 ? '20+' : 'up to ' + n) + 'bb' : 'never') + '">' + k + '<em>' + (n ? (n >= 20 ? '20+' : n) : '') + '</em></span>';
    }
    return h + '</div>' + HAND_KEY + '<div class="tr-legend">Each number is the deepest stack (in big blinds) at which that hand ' + (kind === 'push' ? 'shoves' : 'calls') + ' in equilibrium · big-blind ante · 8-handed</div>';
  }
  function renderPf() {
    if (drill.pfCharts) return renderPfCharts();
    if (!drill.pf) genPf();
    const d = drill.pf;
    const q = plain(d.type === 'push'
      ? 'Tournament · 8 players · the big blind also pays an ante. Everyone folds to you in the <b>' + pusherPos(d.m) + '</b>. You have <b>' + d.S + 'bb</b>, and so does everyone else. All-in or fold?'
      : 'Tournament · 8 players · the big blind also pays an ante. The <b>' + pusherPos(d.m) + '</b> goes all-in for <b>' + d.S + 'bb</b>; everyone has about the same. Everyone folds to you in the <b>' + callerPos(d.m, d.j) + '</b>. Call or fold?');
    let h = '<div class="tr-drill"><div class="tr-row"><span class="tr-dim">Equilibrium push/fold — the strategy nobody can exploit.</span><span style="flex:1"></span><button class="ghost" data-act="pf:charts">📊 Charts</button></div>'
      + '<div class="tr-q">' + q + '</div><div class="tr-hand">' + d.cards.map(c => cardHtml(c, 'lg')).join('') + '<span class="tr-dim">' + esc(handWords(d.k)) + ' (' + d.k + ')</span></div>';
    if (!d.done) h += '<div class="tr-row"><button class="fold" data-act="pf:fold">Fold</button><button data-act="pf:' + (d.type === 'push' ? 'shove' : 'call') + '">' + (d.type === 'push' ? 'All-in' : 'Call') + '</button></div>';
    else h += d.done + pfGrid(d.type, d.m, d.j, d.k) + '<div class="tr-row"><button data-act="pf:next">Next ▶</button></div>';
    $('trMain').innerHTML = h + drillScore('pf', 'correct') + '</div>';
  }
  function answerPf(v) {
    const d = drill.pf; if (!d || d.done) return;
    let right, why;
    if (d.type === 'push') {
      right = PushFold.inPush(d.k, d.m, d.S);
      const lim = PushFold.maxPush(d.k, d.m), share = PushFold.rangePct(PushFold.pushFreq(d.m, d.S));
      why = 'At ' + d.S + 'bb the ' + pusherPos(d.m) + ' shoves ' + r1(share * 100) + '% of hands. ' + d.k + ' shoves here ' + (lim ? (lim >= 20 ? 'at 20bb or less.' : 'up to ' + lim + 'bb.') : 'at no depth up to 20bb.')
        + '\nWith ' + d.m + ' player' + (d.m > 1 ? 's' : '') + ' behind, each one can wake up with a hand — the more behind you, the tighter you shove.';
    } else {
      right = PushFold.inCall(d.k, d.m, d.j, d.S);
      const lim = PushFold.maxCall(d.k, d.m, d.j), eq = PushFold.eqVsRange(PushFold.ix(d.k), PushFold.pushFreq(d.m, d.S)), need = pfNeed(d.m, d.j, d.S);
      why = 'An equilibrium ' + pusherPos(d.m) + ' shoves ' + r1(PushFold.rangePct(PushFold.pushFreq(d.m, d.S)) * 100) + '% at ' + d.S + 'bb. ' + d.k + ' has ' + r1(eq * 100) + '% against that; the pot needs ' + r1(need * 100) + '% to call.'
        + '\n' + d.k + ' calls here ' + (lim ? (lim >= 20 ? 'at 20bb or less.' : 'up to ' + lim + 'bb.') : 'at no depth up to 20bb.') + ' (Chip EV — in a tournament near the money, ICM tightens calls further: try the ICM spots.)';
    }
    const want = d.type === 'push' ? (right ? 'shove' : 'fold') : (right ? 'call' : 'fold');
    const ok = v === want; score('pf', ok);
    d.done = resHtml(V(ok ? 'good' : 'bad', 'Best play: ' + (want === 'shove' ? 'all-in' : want) + (ok ? ' — you had it' : ''), why, 0));
    feed('', '<b>Push/fold: ' + d.k + ', ' + d.S + 'bb, ' + (d.type === 'push' ? pusherPos(d.m) + ' first in' : callerPos(d.m, d.j) + ' vs ' + pusherPos(d.m)) + '</b>' + esc(why));
    renderPf();
  }
  function renderPfCharts() {
    const c = drill.pfChart || (drill.pfChart = { kind: 'push', m: 1, j: 1 });
    const pushBtns = [7, 6, 5, 4, 3, 2, 1].map(m => '<button class="ghost' + (c.kind === 'push' && c.m === m ? ' on' : '') + '" data-act="pf:cp' + m + '">' + pusherPos(m) + ' shove</button>').join('');
    const callBtns = [[1, 1], [2, 2], [2, 1], [3, 3], [5, 5], [7, 7]].map(([m, j]) => '<button class="ghost' + (c.kind === 'call' && c.m === m && c.j === j ? ' on' : '') + '" data-act="pf:cc' + m + j + '">' + callerPos(m, j) + ' calls ' + pusherPos(m) + '</button>').join('');
    $('trMain').innerHTML = '<div class="tr-drill"><div class="tr-row"><button class="ghost" data-act="pf:drill">← Back to the drill</button></div>'
      + '<div class="tr-row tr-views">' + pushBtns + '</div><div class="tr-row tr-views">' + callBtns + '</div>'
      + '<div class="tr-q"><b>' + (c.kind === 'push' ? pusherPos(c.m) + ' — shove when folded to you' : callerPos(c.m, c.j) + ' — call a ' + pusherPos(c.m) + ' shove') + '</b></div>'
      + pfGrid(c.kind, c.m, c.j, '') + '<div class="tr-dim">Computed by Poker Angel: the equilibrium (Nash) for equal stacks with a 1bb big-blind ante, chip EV. Learn these first; near the money, ICM makes calling tighter and shoving into big stacks riskier — the ICM spots drill and tournament mode grade that.</div></div>';
  }

  // ---- ICM spots: real tournament situations, graded in prize money ----
  const SCENARIOS = [
    { id: 'bubble', name: 'Sit-and-go bubble — 4 left, 3 paid', n: 4, pays: [300, 180, 120] },
    { id: 'ft8', name: 'Final table — 8 left, 5 paid', n: 8, pays: [1500, 900, 600, 400, 250] },
    { id: 'ft6', name: 'Final table — 6 left, everyone paid (big jumps at the top)', n: 6, pays: [4000, 2500, 1600, 1100, 800, 600] },
    { id: 'three', name: '3-handed, 2 paid', n: 3, pays: [390, 210] },
    { id: 'hu', name: 'Heads-up for the title', n: 2, pays: [390, 210] },
    { id: 'early', name: 'Early — 6 left, 3 paid (far from the money)', n: 6, pays: [300, 180, 120] },
  ];
  function genIcm() {
    for (let tries = 0; tries < 200; tries++) {
      const sc = pickOf(SCENARIOS), n = sc.n;
      // stacks: a realistic spread (one short, one big) — total about 25bb a player
      const raw = Array.from({ length: n }, () => 0.25 + Math.random() * 1.6);
      const tot = raw.reduce((a, b) => a + b, 0), chipsBB = raw.map(x => Math.max(2, Math.round(x / tot * n * (sc.id === 'early' ? 30 : 22))));
      const names = POS_BY_N[n];                       // position k from the button
      const pre = n === 2 ? [0, 1] : Array.from({ length: n }, (_, k) => (k + 3) % n);
      const bbPos = n === 2 ? 1 : 2, sbPos = n === 2 ? 0 : 1;
      const t = { stacks: chipsBB.slice(), posted: new Array(n).fill(0), dead: 1, payouts: sc.pays.slice(0, n), bb: bbPos, order: [] };
      t.posted[sbPos] = 0.5; t.posted[bbPos] = 1; t.stacks[sbPos] -= 0.5; t.stacks[bbPos] -= 2;
      if (t.stacks.some(s => s <= 0)) continue;
      const shove = Math.random() < 0.55;
      const heroAt = shove ? rnd(n - 1) : 1 + rnd(n - 1);            // index in the preflop order (the BB never shoves first in)
      const hero = pre[heroAt];
      let spot, pusher = -1, behind = 0;
      const k = pickOf(PK_HAND_ORDER);
      if (shove) {
        t.hero = hero; t.order = pre.slice(heroAt + 1);
        const S = Math.min(t.stacks[hero] + t.posted[hero], Math.max.apply(null, t.order.map(j => t.stacks[j] + t.posted[j])));
        if (S > 20) continue;
        spot = PushFold.shoveSpot(t, k);
      } else {
        const pAt = rnd(heroAt); pusher = pre[pAt]; behind = n - 1 - pAt;
        t.posted[pusher] += t.stacks[pusher]; t.stacks[pusher] = 0;
        t.hero = hero;
        if (t.posted[pusher] > 21) continue;
        spot = PushFold.callSpot(t, k, pusher, behind);
      }
      const diff = shove ? spot.shove$ - spot.fold$ : spot.call$ - spot.fold$;
      const pool = sc.pays.reduce((a, b) => a + b, 0);
      if (Math.abs(diff) > 0.06 * pool && Math.random() < 0.7) continue;      // mostly close, instructive spots
      drill.icm = { sc, n, names, chipsBB, t, hero, pusher, behind, shove, k, cards: classCards(k), spot, diff, done: null };
      return;
    }
  }
  function renderIcm() {
    if (!drill.icm) genIcm();
    const d = drill.icm, now = PushFold.icm(d.chipsBB, d.t.payouts);
    const rows = d.chipsBB.map((s, i) => '<tr class="' + (i === d.hero ? 'me' : '') + '"><td>' + POS_FULL[d.names[i]] + ' (' + d.names[i] + ')</td><td>' + (i === d.hero ? 'You' : 'Player ' + (i + 1)) + '</td><td>' + s + 'bb</td><td>' + usd(now[i]) + '</td></tr>').join('');
    const q = d.shove ? 'Everyone folds to you. <b>All-in or fold?</b>' : plain('The <b>' + d.names[d.pusher] + '</b> goes all-in for ' + r1(d.t.posted[d.pusher]) + 'bb; everyone else folds to you. <b>Call or fold?</b>');
    let h = '<div class="tr-drill"><div class="tr-q"><b>' + esc(d.sc.name) + '</b><br><span class="tr-dim">Prizes: ' + d.sc.pays.map((p, i) => ordinal(i + 1) + ' $' + p).join(' · ') + ' · blinds 0.5/1 with a 1bb big-blind ante</span></div>'
      + '<table class="tr-icmt"><tr><th>Seat</th><th>Player</th><th>Chips (in big blinds)</th><th>Worth in prize money now</th></tr>' + rows + '</table>'
      + '<div class="tr-q">You are in the <b>' + POS_FULL[d.names[d.hero]] + '</b>. ' + q + '</div>'
      + '<div class="tr-hand">' + d.cards.map(c => cardHtml(c, 'lg')).join('') + '<span class="tr-dim">' + esc(handWords(d.k)) + ' (' + d.k + ')</span></div>';
    if (!d.done) h += '<div class="tr-row"><button class="fold" data-act="icm:fold">Fold</button><button data-act="icm:go">' + (d.shove ? 'All-in' : 'Call') + '</button></div>';
    else h += d.done + '<div class="tr-row"><button data-act="icm:next">Next spot ▶</button></div>';
    $('trMain').innerHTML = h + drillScore('icm', 'correct') + '</div>';
  }
  function answerIcm(v) {
    const d = drill.icm; if (!d || d.done) return;
    const s = d.spot, best = d.diff >= 0 ? 'go' : 'fold', ok = v === best, verb = d.shove ? 'shove' : 'call';
    const a = stats.drills.icm || (stats.drills.icm = [0, 0, 0]); a[0]++; if (ok) a[1]++; else a[2] = r2(a[2] + Math.abs(d.diff)); saveStats(); dailyAdd('icm');
    let why;
    if (d.shove) {
      const chipsSay = s.shoveChips >= s.foldChips ? 'shove' : 'fold';
      why = 'Prize equity: shove ' + usd(s.shove$) + ' vs fold ' + usd(s.fold$) + ' (' + (d.diff >= 0 ? '+' : '−') + usd(Math.abs(d.diff)) + ' for shoving).'
        + '\nIn chips alone: shove ' + r1(s.shoveChips) + 'bb vs fold ' + r1(s.foldChips) + 'bb — chips say ' + chipsSay + (chipsSay !== (d.diff >= 0 ? 'shove' : 'fold') ? '. ICM disagrees: losing this all-in costs more prize money than winning it gains.' : '.')
        + '\nEveryone folds ' + r1(s.foldEquity * 100) + '% of the time.\n'
        + s.callers.map(c => d.names[c.seat] + ' (' + d.chipsBB[c.seat] + 'bb) needs ' + r1(c.needIcm * 100) + '% equity to call (' + r1(c.needChips * 100) + '% on chips) → calls about ' + r1(c.callPct * 100) + '%').join('\n');
    } else {
      why = d.k + ' has ' + r1(s.eq * 100) + '% against an equilibrium ' + d.names[d.pusher] + ' shoving range (' + r1(s.pusherRangePct * 100) + '% of hands at ' + r1(s.S) + 'bb).'
        + (Math.abs(s.needIcm - s.needChips) < 0.005
          ? '\nYou need ' + r1(s.needChips * 100) + '%' + (d.n === 2 ? ' — heads-up, prize equity is proportional to chips, so ICM and chips agree.' : ' — here ICM barely changes the price.')
          : '\nYou need ' + r1(s.needChips * 100) + '% on chips, but ' + r1(s.needIcm * 100) + '% in prize money — the gap is the ICM “bubble factor”: busting costs more than doubling up gains.')
        + '\nPrize equity: call ' + usd(s.call$) + ' vs fold ' + usd(s.fold$) + '.';
    }
    d.done = resHtml(V(ok ? 'good' : 'bad', 'Best play: ' + (best === 'go' ? (verb === 'shove' ? 'all-in' : verb) : 'fold') + (ok ? ' — you had it' : ' (worth ' + usd(Math.abs(d.diff)) + ' more in prize money)'), why, 0));
    feed('', '<b>Prize money (ICM): ' + esc(d.sc.name) + ' — ' + d.k + '</b>' + esc(why));
    renderIcm();
  }

  // ---- 📘 Learn: the betting strategy, in plain words ----
  // Short lessons in the order a new player needs them. Every figure that the app also uses for
  // grading (chart widths, push/fold ranges) is read from the same tables, so a lesson and a grade
  // can never disagree. Each lesson ends with the drill that practises it.
  function lessons() {
    const w = key => r1(chartWidth(key) * 100) + '%';
    const pf = (m, S) => r1(PushFold.rangePct(PushFold.pushFreq(m, S)) * 100) + '%';
    const t = rows => '<div class="tr-ltable"><table>' + rows.map((r, i) => '<tr>' + r.map(c => i ? '<td>' + c + '</td>' : '<th>' + c + '</th>').join('') + '</tr>').join('') + '</table></div>';
    return [
      { id: 'basics', title: 'How a hand works', practice: null, body:
        '<p>Two players post forced bets before the cards: the <b>small blind</b> (half a big blind) and the <b>big blind</b>. Everyone gets two cards. Then there are four rounds of betting: <b>preflop</b>, the <b>flop</b> (three shared cards), the <b>turn</b> (a fourth) and the <b>river</b> (a fifth). The best five-card hand wins, or the last player left if everyone else folds.</p>'
        + '<p>On your turn you can <b>fold</b> (give up), <b>check</b> (pass, only if nobody has bet), <b>call</b> (match the bet), <b>bet</b> (put chips in first) or <b>raise</b> (make the bet bigger).</p>'
        + '<p>This trainer counts everything in <b>big blinds</b> (bb), so the lessons work at any stakes.</p>' },
      { id: 'position', title: 'Position: why your seat matters', practice: ['pre', 'Preflop drill'], body:
        '<p>Acting <b>last</b> is a big advantage: you see what everyone else did before you decide. The <b>button</b> (BTN) acts last after the flop, so it’s the best seat; the blinds act first, so they’re the worst.</p>'
        + '<p>The earlier you act, the more players are still to come who might have a strong hand — so the earlier your seat, the <b>fewer hands</b> you play. When everyone folds to you, good players raise about:</p>'
        + t([['Seat', 'Raise with about', 'Why'], ['UTG (first to act)', w('rfi.UTG'), '7 players still to act'], ['UTG+1', w('rfi.UTG+1'), '6 to act'], ['LJ', w('rfi.LJ'), '5 to act'], ['HJ', w('rfi.HJ'), '4 to act'], ['CO', w('rfi.CO'), '3 to act'], ['BTN (button)', w('rfi.BTN'), 'only the blinds left, and you act last after the flop'], ['SB', w('rfi.SB'), 'only the big blind left, but you act first after the flop']]) },
      { id: 'preflop', title: 'Before the flop: raise, call or fold', practice: ['pre', 'Preflop drill'], body:
        '<p><b>Everyone folded to you:</b> raise or fold. Don’t just call (limp) — a raise can win the blinds straight away, and it makes weaker hands pay to continue.</p>'
        + '<p><b>Someone raised before you:</b> re-raise (a <b>3-bet</b>) with your very best hands, call with good hands that play well after the flop (pairs, suited aces, suited connectors), and fold the rest. Continue with fewer hands against an early-seat raise — it usually means a stronger hand.</p>'
        + '<p><b>You raised and got re-raised:</b> raise again (a <b>4-bet</b>) with only the very best (QQ+, AK) plus a few bluffs like A5s, call with good hands, and fold the rest. Many hands that were good enough to raise aren’t good enough to keep going.</p>'
        + '<p><b>Someone moves all-in for 100 big blinds:</b> call with QQ, KK, AA and AK; fold everything else.</p>'
        + '<p>The <b>Charts</b> tab shows every one of these ranges hand by hand.</p>' },
      { id: 'potodds', title: 'Pot odds: when a call is worth it', practice: ['odds', 'Pot odds drill'], body:
        '<p>A call is worth making when your <b>chance of winning</b> is bigger than the <b>price</b>. The price is:</p>'
        + '<p class="tr-formula">what you must call ÷ the pot after you call</p>'
        + '<p>Example: the pot is 10bb and your opponent bets 5bb. You call 5 to make a pot of 20, so you need to win 5 ÷ 20 = <b>25%</b> of the time.</p>'
        + t([['They bet', 'You need to win'], ['⅓ of the pot', '20%'], ['½ of the pot', '25%'], ['⅔ of the pot', '28.6%'], ['¾ of the pot', '30%'], ['the size of the pot', '33.3%'], ['2× the pot', '40%']])
        + '<p><b>Counting your chance from outs:</b> an out is a card that makes your hand. With one card to come, your chance is about <b>outs × 2</b>%; with two cards to come (on the flop), about <b>outs × 4</b>%. A flush draw has 9 outs: about 18% on the turn, 36% by the river.</p>'
        + '<p><b>Implied odds:</b> with a draw you can call a little more than the price says, because when you hit you usually win more chips on later streets.</p>' },
      { id: 'postflop', title: 'After the flop: value, bluff or check', practice: ['play', 'Play a hand'], body:
        '<p>Every bet has a job. Ask which one before you bet:</p>'
        + '<p><b>Value bet</b> — you’re probably ahead, and worse hands can call. Bet so they pay you. Checking a strong hand lets them see the next card for free.</p>'
        + '<p><b>Bluff</b> — you’re probably behind, but they may fold a better hand. A bluff only has to work some of the time to pay off; it works best against one player, and against players who fold too much.</p>'
        + '<p><b>Semi-bluff</b> — you’re behind but have a draw. Two ways to win: they fold now, or you hit later. The best bluffs are semi-bluffs.</p>'
        + '<p><b>Check</b> — with medium hands that can’t bet for value and don’t need to bluff. Keep the pot small and see what happens.</p>'
        + '<p><b>Facing a bet:</b> compare your chance of winning with the price (Pot odds). Raise when you’re well ahead or have a strong draw; call when the price is right; otherwise fold.</p>' },
      { id: 'sizing', title: 'Bet sizing: how much to bet', practice: ['play', 'Play a hand'], body:
        '<p>The size of a bet should do its job at the lowest risk. These are the sizes the trainer grades against:</p>'
        + t([['Situation', 'Size', 'Why'],
          ['Open-raise (first in)', '2–3bb (3bb from the SB) + 1bb for each limper', 'wins the blinds often; bigger risks more for the same prize'],
          ['Re-raise (3-bet) in position', '3× their raise', 'you’ll act after them the rest of the hand'],
          ['Re-raise (3-bet) from the blinds', '4× their raise', 'out of position, so charge more'],
          ['4-bet', 'about 2.3× their re-raise', 'already a big part of the stacks'],
          ['Strong hand, board with draws', 'about ¾ pot', 'make draws pay to chase'],
          ['Strong hand, dry board', '½–⅔ pot', 'get called by weaker hands'],
          ['Medium hand for value', '⅓–½ pot', 'get called by worse without building a big pot'],
          ['Semi-bluff with a draw', 'about ⅔ pot', 'enough fold equity, and you can still hit'],
          ['Bluff', '⅓–½ pot', 'needs to work less often; risks less'],
          ['Raising a bet', 'about 3× their bet', 'smaller gives a cheap call'],
          ['12 big blinds or fewer', 'all-in', 'a small raise commits you anyway']])
        + '<p>A board “has draws” when two or more cards share a suit, or the cards are close together (like 8-9-J).</p>' },
      { id: 'reading', title: 'Reading opponents', practice: ['play', 'Play a hand'], body:
        '<p>Don’t guess one exact hand. Think about the <b>range</b> — all the hands a player could have — and narrow it with every action. A raise from UTG is a strong range; a call from the big blind is wide; a big bet on the river after calling twice is usually strong.</p>'
        + '<p>Every bot in this trainer has a style, shown on its seat. Adjust to it:</p>'
        + '<p><b>Practise one adjustment at a time:</b> sit a table of one type and only that lesson is scored. <button class="ghost tr-mini" data-act="learn:table:stations">Calling stations</button> <button class="ghost tr-mini" data-act="learn:table:nits">Nits</button> <button class="ghost tr-mini" data-act="learn:table:maniacs">Maniacs</button> <button class="ghost tr-mini" data-act="learn:table:pros">Tight-aggressive pros</button></p>'
        + t([['Type', 'What they do', 'How to beat them'],
          ['Tight-aggressive', 'few hands, played hard', 'respect their raises; take the blinds when they fold'],
          ['Loose-aggressive', 'many hands, lots of betting', 'call down lighter; trap them with strong hands'],
          ['Nit', 'only premium hands', 'bluff them often; fold when they finally bet big'],
          ['Calling station', 'calls too much, rarely raises', 'never bluff; bet your good hands bigger and more often'],
          ['Maniac', 'bets and raises almost anything', 'let them bluff into your good hands; call more'],
          ['Recreational', 'just calls first in (limps), plays too many hands, calls too much', 'raise their limps with good hands; bet for value; don’t bluff'],
          ['Weak-tight', 'plays reasonable hands but gives up to pressure', 'bet when they check; bluff more; believe them when they raise'],
          ['Trapper', 'checks and calls big hands to spring a trap later', 'be careful when a passive player suddenly raises on the turn or river'],
          ['Shark', 'strong, balanced, few leaks', 'play solid poker; avoid tough spots against them without a good hand']])
        + '<p>Each bot also has a <b>level</b>: beginners make random, unthinking plays about 1 time in 5, casual players about 1 in 10, regulars rarely, and pros never. Choose the table you want with the <b>Opponents</b> setting on the Play tab.</p>' },
      { id: 'short', title: 'Tournaments: short stacks and push/fold', practice: ['pf', 'Push/fold drill'], body:
        '<p>In a tournament the blinds keep rising, so stacks shrink when counted in big blinds. Your plan depends on your stack:</p>'
        + t([['Your stack', 'How to play'], ['40bb or more', 'normal poker, as in the lessons above'], ['20–40bb', 'tighter; avoid calling raises you can’t follow up; re-raising all-in becomes an option'], ['12–20bb', 'raise or fold; re-raise all-in against late-seat raises'], ['under 12bb', '<b>push/fold</b>: go all-in or fold — no small raises, no calls']])
        + '<p>How wide to shove depends on how many players are left to act. With 10bb, equilibrium push/fold shoves about <b>' + pf(5, 10) + '</b> of hands from UTG, <b>' + pf(2, 10) + '</b> from the button and <b>' + pf(1, 10) + '</b> from the small blind. The <b>Push/fold</b> tab has the full charts.</p>' },
      { id: 'icm', title: 'Tournaments: prize money and the bubble (ICM)', practice: ['icm', 'Prize money (ICM) drill'], body:
        '<p>In a tournament your chips are not money — prizes are paid by finishing place. Doubling your stack doesn’t double your prize, but losing it ends your tournament. So near the prizes, <b>losing chips hurts more than winning them helps</b>.</p>'
        + '<p>What that means at the table:</p>'
        + '<p>• <b>Call all-ins tighter</b> near the money (the “bubble”), especially when a shorter stack is about to bust before you.</p>'
        + '<p>• <b>Big stacks can attack</b>: medium stacks can’t afford to call them, so the big stack wins lots of blinds by shoving.</p>'
        + '<p>• <b>Once in the money, every pay jump counts</b> — fold marginal spots while short stacks bust.</p>'
        + '<p>The trainer prices every short-stack decision in prize money. When chips alone and prize money disagree, the grade tells you — that difference is ICM.</p>' },
    ];
  }
  // ---- example hands: each lesson plays a real hand at the table, step by step ----
  // A script fixes the seats, the cards and the board, then lists what happens. Players nobody
  // mentions fold (or check, when that's free) as their turn comes, exactly as at a real table. At a
  // "you" step the reader chooses; the trainer's own grading explains the best play (test/lessons.test.js
  // checks that every script's play IS the best play by the trainer's maths), then the script carries on.
  const LESSON_HANDS = {
    basics: [{ title: 'A whole hand, start to finish', pos: 'BTN', seed: 11, cards: { BTN: 'As Kd', BB: 'Qc 7c' }, board: 'Ks 7d 2c 9h 4s', steps: [
      { say: 'Eight players, 100 big blinds each. You are on the Button — the dealer seat, last to act after the flop. The Small Blind and Big Blind have put in their forced bets, and the first players to act fold.' },
      { you: true, play: ['raise', 2.5], ask: 'Everyone before you folded. It’s your turn.' },
      { pos: 'SB', act: ['fold'], say: 'The Small Blind folds.' },
      { pos: 'BB', act: ['call'], say: 'The Big Blind calls 1.5 more. The pot is 5.5 big blinds, and the flop comes K♠ 7♦ 2♣ — you have top pair with the best kicker.' },
      { pos: 'BB', act: ['check'], say: 'The Big Blind checks to you.' },
      { you: true, play: ['raise', 3], ask: 'Check, or bet?' },
      { pos: 'BB', act: ['call'], say: 'The Big Blind calls. The pot is 11.5 big blinds. The turn is the 9♥.' },
      { pos: 'BB', act: ['check'], say: 'The Big Blind checks again.' },
      { you: true, play: ['raise', 7], ask: 'Check, or bet again?' },
      { pos: 'BB', act: ['fold'], say: 'The Big Blind folds — they had a pair of Sevens, which couldn’t keep calling. You win the pot without a showdown.' },
    ] }],
    position: [
      { title: 'King-Ten from the first seat', pos: 'UTG', seed: 21, cards: { UTG: 'Kc Th' }, board: '2c 3d 4h 5s 6c', steps: [
        { say: 'You are Under the Gun — the first player to act before the flop. Seven players are still to act after you, and any of them could have a strong hand.' },
        { you: true, play: ['fold'], ask: 'You have King-Ten offsuit. Raise or fold?' },
        { end: true, say: 'Folding is right from the first seat: King-Ten offsuit is a decent hand, but with seven players behind it often runs into something better.' },
      ] },
      { title: 'The same hand on the Button', pos: 'BTN', seed: 22, cards: { BTN: 'Kc Th' }, board: '2c 3d 4h 5s 6c', steps: [
        { say: 'Same cards — King-Ten offsuit — but now you are on the Button. Everyone before you folds; only the two blinds are left, and you’ll act last after the flop.' },
        { you: true, play: ['raise', 2.5], ask: 'Raise or fold?' },
        { pos: 'SB', act: ['fold'], say: 'The Small Blind folds.' },
        { pos: 'BB', act: ['fold'], say: 'The Big Blind folds too. You win the blinds without a fight — that’s why late seats raise so many more hands.' },
      ] },
    ],
    preflop: [{ title: 'Re-raising with Queens', pos: 'CO', seed: 31, cards: { CO: 'Qs Qd', UTG: 'Ah Jh' }, board: '8c 4d 2h 9s 3c', steps: [
      { say: 'You are in the Cutoff with a pair of Queens.' },
      { pos: 'UTG', act: ['raise', 2.5], say: 'Under the Gun raises to 2.5 big blinds.' },
      { you: true, play: ['raise', 7.5], ask: 'The players in between fold. It’s your turn, facing a raise.' },
      { pos: 'UTG', act: ['call'], say: 'Everyone else folds and Under the Gun calls. The pot is 16.5 big blinds. The flop: 8♣ 4♦ 2♥ — all small cards, so your Queens are still an overpair.' },
      { pos: 'UTG', act: ['check'], say: 'Under the Gun checks.' },
      { you: true, play: ['raise', 8], ask: 'Check, or bet?' },
      { pos: 'UTG', act: ['fold'], say: 'Under the Gun folds Ace-Jack — two overcards that missed. You win 16.5 big blinds.' },
    ] }],
    potodds: [{ title: 'Calling a draw at the right price — and folding at the wrong one', pos: 'BB', seed: 41, cards: { BB: '8h 7h', BTN: 'Ac Kd' }, board: 'Kh 6h 2c 3d Ts', steps: [
      { say: 'You are in the Big Blind with Eight-Seven of hearts.' },
      { pos: 'BTN', act: ['raise', 2.5], say: 'Everyone folds to the Button, who raises to 2.5 big blinds. The Small Blind folds.' },
      { you: true, play: ['call'], ask: 'Your turn in the Big Blind.' },
      { pos: 'BB', act: ['check'], say: 'The flop is K♥ 6♥ 2♣: you have a flush draw — two more hearts on the board. You check.' },
      { pos: 'BTN', act: ['raise', 3], say: 'The Button bets 3 big blinds into the 5.5 in the pot.' },
      { you: true, play: ['call'], ask: 'Fold, call or raise?' },
      { pos: 'BB', act: ['check'], say: 'The turn is the 3♦ — no heart. You check.' },
      { pos: 'BTN', act: ['raise', 8], say: 'The Button bets 8 big blinds into 11.5 — a bigger bet, and now only one card is left to come.' },
      { you: true, play: ['fold'], ask: 'Fold, or call again?' },
      { end: true, say: 'Same draw, different price: on the flop you had two cards to hit and a small price, so calling paid. On the turn the price went up and only one card was left, so folding was right.' },
    ] }],
    postflop: [{ title: 'Value betting a calling station', pos: 'BTN', seed: 51, cards: { BTN: 'Ac Jc', BB: 'Js 9d' }, board: 'Jh 7s 3d 2c 4s', styles: { BB: ['station', 'casual'] }, steps: [
      { say: 'You are on the Button with Ace-Jack suited. The Big Blind is a calling station — someone who calls far too often and rarely folds a pair.' },
      { you: true, play: ['raise', 2.5], ask: 'Everyone folds to you.' },
      { pos: 'BB', act: ['call'], say: 'The Small Blind folds; the Big Blind calls. The flop: J♥ 7♠ 3♦ — you have top pair, best kicker.' },
      { pos: 'BB', act: ['check'], say: 'The Big Blind checks.' },
      { you: true, play: ['raise', 3], ask: 'Check or bet?' },
      { pos: 'BB', act: ['call'], say: 'The station calls. The turn is the 2♣.' },
      { pos: 'BB', act: ['check'], say: 'Checked to you again.' },
      { you: true, play: ['raise', 7], ask: 'Keep betting?' },
      { pos: 'BB', act: ['call'], say: 'Another call. The river is the 4♠.' },
      { pos: 'BB', act: ['check'], say: 'The Big Blind checks one last time.' },
      { you: true, play: ['raise', 8], ask: 'Last decision: check or bet?' },
      { pos: 'BB', act: ['call'], say: 'The station calls with Jack-Nine — a worse Jack — and you win a big pot. Against players who call too much, keep betting your good hands, and don’t bluff them.' },
    ] }],
    sizing: [{ title: 'Betting big on a board full of draws', pos: 'BTN', seed: 61, cards: { BTN: '9s 9d', BB: 'Ah 4h' }, board: '9h 8h 6c 2s Kd', steps: [
      { say: 'You are on the Button with a pair of Nines.' },
      { you: true, play: ['raise', 2.5], ask: 'Everyone folds to you.' },
      { pos: 'BB', act: ['call'], say: 'The Small Blind folds and the Big Blind calls. The flop: 9♥ 8♥ 6♣ — you have three Nines, but the board is full of possible straights and flushes.' },
      { pos: 'BB', act: ['check'], say: 'The Big Blind checks.' },
      { you: true, play: ['raise', 4], ask: 'Check or bet — and how much?' },
      { pos: 'BB', act: ['call'], say: 'The Big Blind calls (they have a flush draw). The turn is the 2♠ — a blank.' },
      { pos: 'BB', act: ['check'], say: 'Checked to you.' },
      { you: true, play: ['raise', 9], ask: 'Bet again?' },
      { pos: 'BB', act: ['fold'], say: 'The flush draw folds: your big bets made chasing it too expensive. Small bets here would have given them a cheap chance to beat you.' },
    ] }],
    short: [{ title: 'All-in with 10 big blinds', pos: 'BTN', seed: 71, tourBB: 10, cards: { BTN: 'Kd Ts' }, board: '2c 7d 9h 3s 4c', steps: [
      { say: 'A tournament: everyone has 10 big blinds left, and the Big Blind also pays an ante. With a stack this short there is no room for small raises.' },
      { you: true, play: ['raise', 999], ask: 'Everyone folds to you on the Button with King-Ten offsuit.' },
      { pos: 'SB', act: ['fold'], say: 'The Small Blind folds.' },
      { pos: 'BB', act: ['fold'], say: 'The Big Blind folds. You win the blinds and the ante — worth about a quarter of your stack, without seeing a flop.' },
    ] }],
  };
  // Build a scripted hand: the reader sits at the bottom (seat 0) in the script's position.
  function lessonGame(sc) {
    const rng = mulberry(sc.seed || 7);
    const g0 = newGame(rng, 'mixed');
    g0.players.forEach((p, i) => { if (i) { p.style = 'tag'; p.level = 'regular'; } });
    g0.players[0].name = 'You';
    if (sc.tourBB) newTournament(g0, { startBB: sc.tourBB, perLevel: 50 });
    const n = g0.players.length, k = POS.indexOf(sc.pos), button = (n - k) % n;
    g0.button = (button + n - 1) % n;                             // newHand moves it one seat on
    newHand(g0, rng);
    const seatOf = p => (g0.button + POS.indexOf(p)) % n;
    for (const [p, st] of Object.entries(sc.styles || {})) { const q = g0.players[seatOf(p)]; q.style = st[0]; q.level = st[1]; }
    const parse = str => str.split(' ').map(s => ({ r: RK.indexOf(s[0]) + 2, s: SU.indexOf(s[1]) }));
    const fixed = {}; for (const [p, c] of Object.entries(sc.cards || {})) fixed[seatOf(p)] = parse(c);
    const board = sc.board ? parse(sc.board) : [];
    const used = new Set(); Object.values(fixed).flat().concat(board).forEach(c => used.add(cid(c)));
    const rest = []; for (let id = 0; id < 52; id++) if (!used.has(id)) rest.push(fromId(id));
    for (let i = rest.length - 1; i > 0; i--) { const j = Math.floor(rng() * (i + 1)); const t = rest[i]; rest[i] = rest[j]; rest[j] = t; }
    g0.players.forEach((p, i) => { if (!p.out) p.cards = fixed[i] || [rest.pop(), rest.pop()]; });
    // the deck is popped: burn, flop ×3, burn, turn, burn, river
    const b = board.slice(); while (b.length < 5) b.push(rest.pop());
    const burns = [rest.pop(), rest.pop(), rest.pop()];
    g0.deck = rest.concat([b[4], burns[2], b[3], burns[1], b[2], b[1], b[0], burns[0]]);
    g0.lesson = true;
    return g0;
  }
  // Fold (or check, when free) every player whose turn comes before `seat` — the players a script leaves out.
  function autoTo(G, seat) {
    const out = [];
    let guard = 0;
    while (!G.over && G.toAct !== seat && guard++ < 50) {
      const i = G.toAct, free = legal(G, i).toCall === 0;
      act(G, i, { type: free ? 'check' : 'fold' });
      out.push(posOf(G, i) + (free ? ' checks' : ' folds'));
    }
    return out;
  }
  // The trainer's own best play for seat i (the same maths as the grades and the advice).
  function bestKind(G, i, rng) {
    const s = spot(G, i), sp = !s.street && shortSpot(G, i), p = G.players[i];
    if (sp) { const go = gradeShort(G, i, sp.type === 'shove' ? 'raise' : 'call', p.bet + p.stack); return go.v === 'good' ? (sp.type === 'shove' ? 'raise' : 'call') : 'fold'; }
    if (!s.street) return preflopAdvice(s.k, s).best;
    const E = equityVsRanges(s.cards, s.board, s.opps, 6000, rng);
    const kinds = s.toCall > 0 ? ['raise', 'call', 'fold'] : ['raise', 'check'];
    const rated = kinds.map(k => ({ k, G: gradePost(s, k, E) }));
    return (rated.find(r => r.G.v === 'good') || rated.find(r => r.G.v === 'ok') || rated[0]).k;
  }
  // Grade the reader's choice at a "you" step, like a real decision (without playing it).
  function gradeChoice(G, i, kind, to) {
    const s = spot(G, i), L = legal(G, i);
    let k = kind;
    if (k === 'raise' && (!L.canRaise || !(to > G.curBet))) k = 'call';
    if (k === 'call' && L.toCall === 0) k = 'check';
    if (k === 'check' && L.toCall > 0) k = 'fold';
    const E = s.street ? equityVsRanges(s.cards, s.board, s.opps, 4000) : null;
    const short = !s.street && gradeShort(G, i, k, to);
    const Gr = short || withSizing(s.street ? gradePost(s, k, E) : gradePre(s, k), s, k, Math.max(L.minTo, Math.min(L.maxTo, half(Number(to) || 0))), E);
    return { kind: k, verb: verbOf(k, s), G: Gr };
  }
  // ---- the example-hand player (Learn tab) ----
  function startExample(id, si) {
    const list = LESSON_HANDS[id]; if (!list || !list[si]) return;
    const sc = list[si];
    drill.ex = { id, si, sc, g: lessonGame(sc), i: 0, notes: [], feedback: null, waiting: false, done: false };
    exAdvance();
  }
  // Play script steps until one needs the reader: a note to read (Next) or a decision to make.
  function exAdvance() {
    const X = drill.ex; if (!X || X.done) return renderExample();
    X.feedback = null;
    const st = X.sc.steps[X.i];
    if (!st || X.g.over) { X.done = true; return renderExample(); }
    if (st.end) { X.notes.push(st.say); X.done = true; return renderExample(); }
    if (st.you) {
      const auto = autoTo(X.g, 0);
      if (auto.length) X.notes.push(auto.join(', ') + '.');
      X.notes.push(st.ask); X.waiting = true; return renderExample();
    }
    if (st.pos) {
      const seat = (X.g.button + POS.indexOf(st.pos)) % X.g.players.length;
      autoTo(X.g, seat);
      if (!X.g.over && X.g.toAct === seat) act(X.g, seat, { type: st.act[0], to: st.act[1] });
    }
    if (st.say) X.notes.push(st.say);
    X.i++;
    if (X.g.over && X.i >= X.sc.steps.length) X.done = true;
    renderExample();
  }
  function exChoose(kind) {
    const X = drill.ex; if (!X || !X.waiting) return;
    const st = X.sc.steps[X.i], L = legal(X.g, 0);
    const to = kind === 'raise' ? (st.play[0] === 'raise' ? st.play[1] : (sizes()[0] || {}).to) : 0;
    const saved = { g, me }; g = X.g; me = 0;
    let res; try { res = gradeChoice(X.g, 0, kind === 'allin' ? 'raise' : kind, kind === 'allin' ? L.maxTo : to); res.detail = detailFor(X.g, 0); } finally { g = saved.g; me = saved.me; }
    X.feedback = res;
    act(X.g, 0, { type: st.play[0], to: st.play[1] });         // the hand carries on with the best play
    X.waiting = false; X.i++;
    if (X.g.over && X.i >= X.sc.steps.length) X.done = true;
    renderExample();
  }
  function renderExample() {
    const X = drill.ex, list = LESSON_HANDS[X.id], m = $('trMain');
    const saved = { g, me, room, show: opts.showBots };
    let felt, choices = '';
    g = X.g; me = 0; room = null; opts.showBots = false;
    try {
      felt = feltHtml();
      if (X.waiting) {
        const L = legal(X.g, 0), st = X.sc.steps[X.i], b = ['<button class="fold" data-act="ex:fold">Fold</button>'];
        b.push(L.toCall > 0 ? '<button data-act="ex:call">Call ' + bbs(L.toCall) + '</button>' : '<button data-act="ex:check">Check</button>');
        if (L.canRaise) {
          const to = st.play[0] === 'raise' ? Math.min(st.play[1], L.maxTo) : ((sizes()[0] || {}).to || L.minTo);
          if (to < L.maxTo - 0.01) b.push('<button class="raise" data-act="ex:raise">' + (X.g.curBet > 0 && X.g.street === 0 || L.toCall > 0 ? 'Raise to ' : 'Bet ') + bbs(to) + '</button>');
          b.push('<button class="raise" data-act="ex:allin">All-in ' + bbs(L.maxTo) + '</button>');
        }
        choices = b.join('');
      }
    } finally { g = saved.g; me = saved.me; room = saved.room; opts.showBots = saved.show; }
    const last = X.notes.slice(-1)[0] || '', earlier = X.notes.slice(0, -1);
    const fb = X.feedback ? '<div class="tr-explain"><b>' + esc(plain('You chose: ' + X.feedback.verb + ' · ' + X.feedback.G.head)) + '</b><div class="tr-why">' + fmtWhy(X.feedback.G.why) + '</div>' + detailHtml(X.feedback.detail, true) + '</div>' : '';
    const end = X.done ? (X.g.over && X.g.result ? '<div class="tr-dim">' + esc(plain(X.g.result.wins.map(w => (w.i === 0 ? 'You win ' : X.g.players[w.i].name + ' wins ') + bbs(r2(w.amt)) + (w.name ? ' with ' + w.name : '')).join(' · '))) + '</div>' : '')
      + '<div class="tr-row">' + (list[X.si + 1] ? '<button class="primary" data-act="ex:nextex">Next example ▶</button>' : '') + '<button class="ghost" data-act="ex:again">Play it again</button><button class="ghost" data-act="ex:close">Back to the lesson</button></div>' : '';
    const controls = X.waiting ? '<div class="tr-actions">' + choices + '</div>' : (X.done ? '' : '<div class="tr-actions"><button class="primary" data-act="ex:next">Next ▶</button></div>');
    m.innerHTML = '<div class="tr-replay-head"><button class="ghost" data-act="ex:close">← Lessons</button><b>Example hand · ' + esc(X.sc.title) + '</b>'
      + (list.length > 1 ? '<span class="tr-dim">' + (X.si + 1) + ' of ' + list.length + '</span>' : '') + '</div>'
      + '<div class="tr-felt-wrap"><div class="tr-felt">' + felt + '</div></div>'
      + controls;
    setPanel('<div class="tr-explain tr-narrate"><b>' + esc(plain(last)) + '</b>' + (earlier.length ? '<details><summary>What happened so far</summary><div class="tr-why">' + esc(plain(earlier.join('\n'))) + '</div></details>' : '') + end + '</div>' + fb);
  }

  // ---- 🌙 sleep story ----
  // A 20-minute recording (audio/sleep-story.mp3). One player for the whole page, so it keeps playing
  // when the Learn tab is re-drawn or you switch tabs.
  let sleepAudio = null;
  const mmss = t => Math.floor(t / 60) + ':' + String(Math.floor(t % 60)).padStart(2, '0');
  function sleepUi() {
    const a = sleepAudio, btn = document.querySelector('[data-act="sleep:play"]'), pos = $('trSleepPos');
    const playing = a && !a.paused && !a.ended;
    if (btn) btn.textContent = playing ? '⏸ Pause' : a && a.currentTime > 0 && !a.ended ? '▶ Carry on' : '▶ Play';
    if (pos) pos.textContent = a && a.duration ? mmss(a.currentTime) + ' of ' + mmss(a.duration) : '20 minutes';
  }
  function sleepAct(v) {
    if (!sleepAudio) {
      sleepAudio = new Audio('audio/sleep-story.mp3');
      ['timeupdate', 'play', 'pause', 'ended', 'loadedmetadata'].forEach(e => sleepAudio.addEventListener(e, sleepUi));
      sleepAudio.addEventListener('error', () => toast('The sleep story couldn’t be played', 'red'));
    }
    if (v === 'play') { if (sleepAudio.paused || sleepAudio.ended) { hush(); sleepAudio.play().catch(e => console.error('sleep story', e)); } else sleepAudio.pause(); }
    if (v === 'stop') { sleepAudio.pause(); sleepAudio.currentTime = 0; }
    sleepUi();
  }
  function sleepCard() {
    return '<div class="tr-q tr-sleep"><b>🌙 Sleep story: The Quiet Table</b> <span class="tr-dim">· about 20 minutes</span><br>'
      + '<span class="tr-dim">A calm bedtime story, read slowly, that carries the habits of good players — patience, folding without regret, position, watching how others play, betting your good hands, and letting bad luck pass. Play it in bed with the screen off. The file is also in the Poker Angel folder to copy to your phone.</span>'
      + '<div class="tr-row"><button data-act="sleep:play">▶ Play</button><button class="ghost" data-act="sleep:stop">⏹ Stop</button><span class="tr-dim" id="trSleepPos">about 20 minutes</span></div></div>';
  }
  function renderLearn() {
    if (drill.ex) return renderExample();
    const L = lessons(), open = drill.learnOpen || 'basics';
    $('trMain').innerHTML = '<div class="tr-drill tr-learn">' + sleepCard() + '<div class="tr-q"><b>Learn the betting strategy</b><br><span class="tr-dim">Short lessons in order. The trainer grades you against exactly these rules.</span></div>'
      + L.map((x, i) => '<details' + (x.id === open ? ' open' : '') + ' data-lesson="' + x.id + '"><summary><span class="tr-lnum">' + (i + 1) + '</span>' + esc(x.title) + '</summary><div class="tr-lbody">' + x.body
        + '<div class="tr-row">' + (LESSON_HANDS[x.id] ? '<button class="primary" data-act="ex:start:' + x.id + '">▶ Play the example hand' + (LESSON_HANDS[x.id].length > 1 ? 's' : '') + '</button>' : '')
        + (x.practice ? '<button class="ghost" data-act="learn:' + x.practice[0] + '">Practise: ' + esc(x.practice[1]) + '</button>' : '') + '</div></div></details>').join('')
      + '</div>';
    $('trMain').querySelectorAll('details').forEach(d => d.addEventListener('toggle', () => { if (d.open) drill.learnOpen = d.dataset.lesson; }));
    sleepUi();
  }

  // ---- charts & stats ----
  function gridHtml(viewId, me) {
    const vw = VIEWS.find(v => v.id === viewId); if (!vw) return '';
    const R = vw.raise ? chart(vw.raise) : new Set(), C = vw.call ? chart(vw.call) : new Set();
    let h = '<div class="tr-grid">';
    for (let i = 12; i >= 0; i--) for (let j = 12; j >= 0; j--) {
      const a = RK[i], b = RK[j], k = i === j ? a + a : i > j ? a + b + 's' : b + a + 'o';
      h += '<span class="' + (R.has(k) ? 'r' : C.has(k) ? 'c' : '') + (k === me ? ' me' : '') + '" title="' + k + '">' + k + '</span>';
    }
    return h + '</div>';
  }
  const HAND_KEY = '<div class="tr-key">How hands are written: <b>AKs</b> = Ace-King suited (both cards the same suit) · <b>AKo</b> = Ace-King offsuit (different suits) · <b>TT</b> = a pair of Tens · <b>T</b> = Ten · suited hands sit above the diagonal, offsuit below, pairs on it.</div>';
  function legendHtml(viewId) {
    const vw = VIEWS.find(v => v.id === viewId); if (!vw) return '';
    const isOpen = /^rfi\./.test(viewId);
    const w = key => key ? r1(chartWidth(key) * 100) + '%' : '';
    return '<div class="tr-legend"><span class="r"></span>' + (isOpen ? 'Raise' : viewId === 'vs4' ? 'All-in' : viewId === 'vs3' ? '4-bet' : '3-bet') + ' ' + w(vw.raise)
      + (vw.call ? ' <span class="c"></span>Call ' + w(vw.call) : '') + ' <span></span>Fold · % = share of all starting hands</div>' + HAND_KEY;
  }
  function renderCharts() {
    const vw = VIEWS.find(v => v.id === chartView) || VIEWS[0];
    $('trMain').innerHTML = '<div class="tr-drill"><div class="tr-row tr-views">' + VIEWS.map(v => '<button class="ghost' + (v.id === vw.id ? ' on' : '') + '" data-act="chart:' + v.id + '">' + esc(v.name) + '</button>').join('') + '</div>'
      + '<div class="tr-q"><b>' + esc(vw.name) + '</b></div>' + gridHtml(vw.id, '') + legendHtml(vw.id)
      + '<div class="tr-dim">Simplified 100bb charts for an 8-handed table: a sound baseline to learn, not a solver’s exact output. Suited hands sit above the diagonal, offsuit below, pairs on it.</div></div>';
  }
  function drillScore(key, what) {
    const a = stats.drills[key];
    if (key === 'eq') return '<div class="tr-dim">Equity drill: ' + a[0] + ' answered · ' + a[1] + ' within 5 points · average error ' + (a[0] ? r1(a[2] / a[0]) : 0) + ' points</div>';
    if (key === 'icm') return '<div class="tr-dim">ICM spots: ' + a[1] + ' of ' + a[0] + ' correct' + (a[0] ? ' (' + Math.round(a[1] / a[0] * 100) + '%)' : '') + ' · prize equity given away ' + usd(a[2]) + '</div>';
    return '<div class="tr-dim">' + a[1] + ' of ' + a[0] + ' ' + what + (a[0] ? ' (' + Math.round(a[1] / a[0] * 100) + '%)' : '') + '</div>';
  }
  // Each sitting as the difference between snapshots, newest first, plus the sitting in progress.
  function sittingsHtml() {
    const S = (stats.sessions || []).slice(), cur = snapOf(); cur.current = true;
    const all = S.concat([cur]), rows = [];
    for (let i = all.length - 1; i >= 0; i--) {
      const a = all[i], b = i > 0 ? all[i - 1] : { hands: 0, net: 0, good: 0, ok: 0, bad: 0, loss: 0, street: [], drills: {} };
      const hands = a.hands - b.hands, good = a.good - b.good, ok = a.ok - b.ok, bad = a.bad - b.bad, dec = good + ok + bad;
      if (!hands && !dec && !a.current) continue;
      const st = k => { const x = (a.street || [])[k] || [0, 0, 0], y = (b.street || [])[k] || [0, 0, 0]; const g2 = x[0] - y[0], o2 = x[1] - y[1], b2 = x[2] - y[2], n = g2 + o2 + b2; return n ? Math.round((g2 + o2) / n * 100) + '%' : '—'; };
      const dr = (k, idx) => { const x = (a.drills || {})[k] || [], y = (b.drills || {})[k] || []; const n = (x[0] || 0) - (y[0] || 0), r = (x[idx] || 0) - (y[idx] || 0); return n ? r + '/' + n : '—'; };
      rows.push('<tr' + (a.current ? ' class="me"' : '') + '><td>' + (a.current ? 'This sitting' : new Date(a.when).toLocaleDateString(undefined, { day: 'numeric', month: 'short' })) + '</td><td>' + hands + '</td><td>' + (a.net - b.net >= 0 ? '+' : '') + r1(a.net - b.net) + '</td><td>' + (dec ? Math.round((good + ok) / dec * 100) + '%' : '—') + '</td><td>' + st(0) + '</td><td>' + [1, 2, 3].map(st).filter(x => x !== '—').join(' / ') + '</td><td>' + dr('pre', 1) + '</td><td>' + dr('pf', 1) + '</td></tr>');
    }
    if (!rows.length) return '';
    return '<div class="tr-q"><b>Sittings</b> <span class="tr-dim">— each row is one sitting (a break of two hours ends one): hands, result in big blinds, how often your decisions matched the best play, preflop and after the flop, and the drills.</span></div>'
      + '<div class="tr-tscroll"><table class="tr-icmt"><tr><th>When</th><th>Hands</th><th>Result</th><th>Matched</th><th>Preflop</th><th>Flop / turn / river</th><th>Preflop drill</th><th>Push/fold drill</th></tr>' + rows.join('') + '</table></div>';
  }
  function renderStats() {
    const s = stats, dec = s.good + s.ok + s.bad, pc = (a, b) => b ? Math.round(a / b * 100) + '%' : '—';
    const tile = (l, v) => '<div class="tr-stat"><small>' + l + '</small><b>' + v + '</b></div>';
    const leaks = Object.keys(s.leaks).sort((a, b) => s.leaks[b] - s.leaks[a]).slice(0, 8);
    const D = s.drills;
    $('trMain').innerHTML = '<div class="tr-drill">' + dailyHtml() + '<div class="tr-q"><b>Your play</b></div><div class="tr-stats">'
      + tile('Hands played', s.hands) + tile('Result', (s.net >= 0 ? '+' : '') + bbs(s.net)) + tile('Big blinds won per 100 hands', s.hands ? r1(s.net / s.hands * 100) : '—')
      + tile('Hands you chose to play (VPIP)', pc(s.vpip, s.hands)) + tile('Hands you raised before the flop (PFR)', pc(s.pfr, s.hands))
      + tile('Decisions explained', dec) + tile('Matched the best play (or close)', pc(s.good + s.ok, dec)) + tile('Differed from the best play', s.bad) + tile('Chips those cost (big blinds)', r1(s.loss)) + tile('Hints used', s.hints) + tile('Coached on other sites', s.coach || 0)
      + '</div><div class="tr-dim">VPIP = Voluntarily Put money In the Pot; PFR = Pre-Flop Raise. At a 6-player table, good players play about 22–28% of hands and raise a few points fewer than that. Results over a few hundred hands are mostly luck — the decision grades are the number to watch.</div>'
      + '<div class="tr-q"><b>Where your choices most often differ from the best play</b></div>'
      + (leaks.length ? '<div class="tr-res">' + leaks.map(k => s.leaks[k] + ' × ' + esc(plain(k.replace(/^Best play: /, 'when the best play was ')))).join('\n') + '</div>' : '<div class="tr-dim">None recorded yet.</div>')
      + '<div class="tr-q"><b>Drills</b></div><div class="tr-stats">'
      + tile('Preflop', D.pre[1] + '/' + D.pre[0]) + tile('Pot odds', D.odds[1] + '/' + D.odds[0]) + tile('Equity (avg error)', D.eq[0] ? r1(D.eq[2] / D.eq[0]) + ' pts' : '—')
      + tile('Outs', D.outs[1] + '/' + D.outs[0]) + tile('Showdown', D.sd[1] + '/' + D.sd[0])
      + tile('Push/fold', D.pf[1] + '/' + D.pf[0]) + tile('Prize money (ICM)', D.icm[1] + '/' + D.icm[0])
      + '</div><div class="tr-q"><b>Tournaments</b></div><div class="tr-stats">'
      + tile('Played', s.tourneys || 0) + tile('Won', s.wins || 0) + tile('In the money', pc(s.itm || 0, s.tourneys || 0))
      + tile('Return on buy-ins', s.tourCost ? Math.round(((s.tourPrize || 0) - s.tourCost) / s.tourCost * 100) + '%' : '—')
      + tile('Prize money those choices cost', usd((s.lossUsd || 0) + (D.icm[2] || 0)))
      + '</div><div class="tr-dim">A handful of tournaments is mostly luck; return on buy-ins means something after hundreds. How closely your choices match the best play is the number you control.</div>'
      + sittingsHtml()
      + '<div class="tr-row"><button class="ghost" data-act="stats:endsit">End this sitting now</button><button class="ghost" data-act="stats:reset">Reset all stats</button></div></div>';
  }

  function renderTabs() { $('trTabs').innerHTML = TABS.map(t => '<button class="ghost' + (t[0] === tab ? ' on' : '') + '" data-tab="' + t[0] + '">' + t[1] + '</button>').join(''); }
  function renderMain() {
    if (!shown) return;
    setPanel('');
    ({ play: renderPlay, learn: renderLearn, hands: renderHands, pf: renderPf, icm: renderIcm, pre: renderPre, odds: renderOdds, eq: renderEq, outs: renderOuts, sd: renderSd, charts: renderCharts, stats: renderStats }[tab] || renderPlay)();
    if (tab !== 'play') renderSpot();
  }
  function setTab(t) {
    tab = t; renderTabs(); renderMain();
    if (t === 'play' && !room && g && !g.over && !isHuman(g.players[g.toAct])) step();
  }

  const HANDLERS = {
    play: (v, b) => {
      if (v === 'continue') { const p = myPending(); if (p) ackId = p.id; if (g && g.over && fastFolding()) return startHand(); renderPlay(); if (!isGuest()) { if (stepBots()) watchPlay(false); else step(); } return; }
      if (v === 'next') { const p = myPending(); if (p) ackId = p.id; if (g && g.tour && g.tour.done) freshTable(); return startHand(); }
      if (v === 'hint') return hint();
      if (v === 'auto') return autoStart();
      if (v === 'sleep') return sleepStory(+b.dataset.v || 30, true);
      if (v === 'autostop') return autoStop();
      if (v === 'autospeed') { opts.autoSpeed = b.dataset.v; saveOpts(); if (auto) auto.speed = opts.autoSpeed; renderPlay(); return; }
      if (v === 'automins') { opts.autoMins = +b.dataset.v || 0; saveOpts(); if (auto) auto.endAt = opts.autoMins ? auto.t0 + opts.autoMins * 60000 : 0; renderPlay(); return; }
      if (v === 'wnext' || v === 'wall') return watchPlay(v === 'wall');
      if (v === 'ai') return askAI(b);
      if (v === 'copy') { try { navigator.clipboard.writeText(historyText(g, decisions)); toast('Hand history copied', 'green'); } catch (e) {} return; }
      if (v === 'raise') return heroAct('raise', parseFloat(b.dataset.to));
      if (v === 'raiseTo') { const x = parseFloat(($('trTo') || {}).value); if (!isFinite(x)) return; return heroAct('raise', x); }
      heroAct(v);
    },
    learn: v => {
      if (v.indexOf('table:') === 0) { opts.field = v.slice(6); saveOpts(); freshTable(); setTab('play'); startHand(); toast(FIELDS[opts.field].name, 'green'); return; } drill.ex = null; setTab(v); },
    sleep: v => sleepAct(v),
    ui: v => {
      if (v === 'detail') { opts.detail = !opts.detail; saveOpts(); renderMain(); }
      if (v === 'speak') { const t = forSpeech(panelText()); markSaid(t); speak(t); }
      if (v === 'speaktoggle') { opts.speak = !opts.speak; saveOpts(); spokenLast = ''; said = new Set(); if (!opts.speak) hush(); renderMain(); }
      if (v === 'hush') hush();
      if (v === 'voicetry') speak(VOICE_SAMPLE);
      if (v === 'freshtalk') freshTalk();
    },
    ex: v => {
      if (v.indexOf('start:') === 0) return startExample(v.slice(6), 0);
      const X = drill.ex; if (!X) return;
      if (v === 'next') return exAdvance();
      if (v === 'nextex') return startExample(X.id, X.si + 1);
      if (v === 'again') return startExample(X.id, X.si);
      if (v === 'close') { drill.learnOpen = X.id; drill.ex = null; return renderLearn(); }
      exChoose(v);
    },
    hist: v => {
      if (v.indexOf('open:') === 0) { const rec = history.find(h => h.id === v.slice(5)); if (rec) drill.replay = { rec, step: 0 }; return renderHands(); }
      const R = drill.replay; if (!R && v !== 'close') return;
      if (v === 'close') drill.replay = null;
      else if (v === 'first') R.step = 0;
      else if (v === 'prev') R.step = Math.max(0, R.step - 1);
      else if (v === 'next') R.step = Math.min(R.rec.acts.length, R.step + 1);
      else if (v === 'last') R.step = R.rec.acts.length;
      else if (v === 'whatif') { const d = R.rec.dec.find(x => x.at === R.step - 1); if (d) { let res = null; try { res = whatIf(R.rec, d); } catch (e) { console.error('what if', e); } R.whatIf = { at: d.at, res }; } }
      renderHands();
    },
    tour: v => {
      if (v === 'start' || v === 'again') return startTournament();
      if (v === 'menu') { freshTable(); broadcast(); renderPlay(); }
    },
    rec: (v, b) => { const n = b && b.dataset.name; if (v === 'start') recStart(); else if (v === 'stop') recStop(); else if (v === 'play') recPlayback(n); else if (v === 'save') recSave(n); else if (v === 'delete') recDelete(n); else if (v === 'clone') recClone(n); else if (v === 'more') recStart(n, true); else if (v === 'inbox') inboxOpen(); else if (v === 'inboxclose') inboxClose(); else if (v === 'connect') sendConnect(($('trSendCode') || {}).value); else if (v === 'send') sendVoice(); else if (v === 'usepc') usePcVoice(n); else if (v === 'import') { const f = $('trRecFile'); if (f) { f.onchange = () => { recImport(f.files && f.files[0]); f.value = ''; }; f.click(); } } },
    room: v => {
      const nameIn = $('trName');
      if (nameIn) ls(NAME_KEY, String(nameIn.value || '').trim().slice(0, 16));
      if (v === 'host') return hostTable();
      if (v === 'join') return joinTable(($('trCode') || {}).value);
      if (v === 'leave') return leaveRoom();
      if (v === 'copy' && room) { try { navigator.clipboard.writeText(room.code); toast('Table code ' + room.code + ' copied', 'green'); } catch (e) {} }
      if (v === 'invite' && room) { try { navigator.clipboard.writeText(INVITE(room.code)); toast('Invitation copied — paste it into a message', 'green'); } catch (e) {} }
    },
    pf: v => {
      if (v === 'next') { genPf(); return renderPf(); }
      if (v === 'charts') { drill.pfCharts = true; return renderPf(); }
      if (v === 'drill') { drill.pfCharts = false; return renderPf(); }
      if (/^cp\d$/.test(v)) { drill.pfChart = { kind: 'push', m: +v[2], j: 1 }; return renderPf(); }
      if (/^cc\d\d$/.test(v)) { drill.pfChart = { kind: 'call', m: +v[2], j: +v[3] }; return renderPf(); }
      answerPf(v === 'shove' ? 'shove' : v === 'call' ? 'call' : 'fold');
    },
    icm: v => { if (v === 'next') { genIcm(); renderIcm(); } else answerIcm(v); },
    pre: v => { if (v === 'next') { genPre(); renderPre(); } else answerPre(v); },
    odds: v => { if (v === 'next') { genOdds(); renderOdds(); } else answerOdds(); },
    eq: v => { if (v === 'next') { genEq(); renderEq(); } else answerEq(); },
    outs: v => { if (v === 'next') { genOuts(); renderOuts(); } else answerOuts(); },
    sd: v => { if (v === 'next') { genSd(); renderSd(); } else answerSd(v); },
    chart: v => { chartView = v; renderCharts(); },
    // two presses, no dialog (pages on claude.ai can't show confirm())
    stats: (v, b) => {
      if (v === 'endsit') { toast(closeSitting(true) ? 'Sitting closed — it’s on the list' : 'Nothing new since the last sitting', ''); return renderStats(); }
      if (v !== 'reset') return;
      if (!drill.resetArmed) { drill.resetArmed = true; b.textContent = 'Press again to reset everything'; setTimeout(() => { drill.resetArmed = false; if (tab === 'stats') renderStats(); }, 4000); return; }
      drill.resetArmed = false; stats = DEF_STATS(); saveStats(); renderStats(); toast('Stats reset', '');
    },
  };

  function open() {
    shown = true; $('trainer').classList.add('show'); $('trainer').setAttribute('aria-hidden', 'false');
    closeSitting(false);                                                           // back after a break: the last sitting is closed off
    const nav = $('navTrainer'); if (nav) nav.classList.add('on');
    renderTabs(); renderMain();
    if (!room && g && !g.over && !isHuman(g.players[g.toAct])) step();   // solo: the bots pick up where they left off
  }
  function close() {
    shown = false; roomStop(); clearTimeout(chatterTimer);
    if (!room) token++;                                            // a friends' table carries on while you're in the coach

    $('trainer').classList.remove('show'); $('trainer').setAttribute('aria-hidden', 'true');
    const nav = $('navTrainer'); if (nav) nav.classList.remove('on');
  }
  function wire() {
    ['pointerdown', 'touchend', 'click', 'keydown'].forEach(ev => document.addEventListener(ev, unlockVoice, { capture: true, passive: true }));
    // Anything that breaks shows up on the page, so a phone can tell us what went wrong.
    const showErr = msg => { try { let b = document.getElementById('paErr'); if (!b) { b = document.createElement('div'); b.id = 'paErr'; b.style.cssText = 'position:fixed;left:8px;right:8px;top:8px;z-index:99999;background:#7f1d1d;color:#fff;padding:10px 12px;border-radius:10px;font:13px/1.4 system-ui;white-space:pre-wrap;word-break:break-word;box-shadow:0 10px 30px rgba(0,0,0,.5)'; b.onclick = () => b.remove(); document.body.appendChild(b); } b.textContent = '⚠ Poker Angel hit a problem (tap to hide): ' + msg + ' — ' + navigator.userAgent.slice(0, 120); } catch (e) {} };
    window.addEventListener('error', e => showErr((e.message || 'error') + (e.filename ? ' @ ' + e.filename.split('/').pop() + ':' + e.lineno : '')));
    window.addEventListener('unhandledrejection', e => showErr('promise: ' + (e.reason && (e.reason.message || e.reason) || 'rejected')));
    loadLib().then(() => { if (HAS_LIB && typeof Peer === 'function') inboxOpen(); if (shown && tab === 'play' && !g) renderPlay(); });
    if (!HAS_LIB && typeof Peer === 'function' && ls(PCCODE_KEY) && !sendTo) setTimeout(() => sendConnect(ls(PCCODE_KEY)), 800);   // the phone links back to the PC on its own
    document.addEventListener('click', () => { if (actx && actx.state === 'suspended') actx.resume().catch(() => {}); }, true);
    loadVoiceCfg();
    if (CAN_SPEAK) { try { speechSynthesis.onvoiceschanged = () => { if (shown && tab === 'play') renderPlay(); }; } catch (e) {} }
    const nav = $('navTrainer'); if (nav) nav.onclick = () => (shown ? close() : open());
    $('trTabs').onclick = (e) => { const b = pick(e, 'data-tab'); if (b) setTab(b.dataset.tab); };
    const onAct = (e) => {
      const b = pick(e, 'data-act'); if (!b || b.disabled) return;
      const at = b.dataset.act.indexOf(':'), ns = b.dataset.act.slice(0, at), v = b.dataset.act.slice(at + 1);
      if (HANDLERS[ns]) HANDLERS[ns](v, b);
    };
    $('trMain').onclick = onAct;
    const side = $('trSide'); if (side) side.onclick = onAct;    // Continue / Got it / the numbers switch live in the right-hand column
    $('trMain').onchange = (e) => {
      if (e.target && e.target.id === 'trField') { opts.field = e.target.value; saveOpts(); return; }
      if (e.target && e.target.id === 'trDepth') { opts.depth = Number(e.target.value) || 100; saveOpts(); if (g && !g.tour) g.depth = opts.depth; return; }
      const r = pick(e, 'data-room');
      if (r && isHost()) { room.faceUp = !!r.checked; broadcast(); renderPlay(); feed('', '<b>Cards: ' + (room.faceUp ? 'face up for everyone' : 'own cards only') + '</b>' + (room.faceUp ? 'Every card and grade is shown as it happens.' : 'Everyone’s cards and grades are revealed when each hand ends.')); return; }
      const sel = pick(e, 'data-sel'); if (sel && sel.dataset.sel === 'level') return setLevel(sel.value);
      if (sel && sel.dataset.sel === 'voice') {
        if (/^__pcv:/.test(sel.value)) { opts.pcVoice = sel.value.slice(6); saveOpts(); if (pcLinked()) speak(VOICE_SAMPLE); else toast('Open Poker Angel on the PC and tap Connect under 🎙 Voices to use ' + opts.pcVoice, 'red'); return; }
        opts.pcVoice = ''; saveOpts();
        if (/^__own:/.test(sel.value)) { const name = sel.value.slice(6), id = libVoiceId(name); if (id && window.api && window.api.setTts) { window.api.setTts({ engine: 'own', voice: id, voiceName: name }).then(() => { voiceChanged(); setTimeout(() => speak(VOICE_SAMPLE), 400); }); } return; }
        opts.voice = sel.value; saveOpts(); speak(VOICE_SAMPLE); return;
      }
      if (sel && sel.dataset.sel === 'coachVoice') {
        if (sel.value === '__pc') { window.api.setTts({ engine: 'local' }).then(() => { voiceChanged(); setTimeout(() => speak(VOICE_SAMPLE), 400); }); return; }
        const id = libVoiceId(sel.value); if (id) window.api.setTts({ engine: voiceCfg.engine === 'local' ? 'own' : voiceCfg.engine, voice: id, voiceName: sel.value }).then(() => { voiceChanged(); setTimeout(() => speak(VOICE_SAMPLE), 400); });
        return;
      }
      if (sel && sel.dataset.sel === 'speakRate') { opts.speakRate = parseFloat(sel.value) || 1; saveOpts(); speak(VOICE_SAMPLE); return; }
      if (sel && /^(chatterVol|chatterOften|roomVol)$/.test(sel.dataset.sel)) { opts[sel.dataset.sel] = sel.value; saveOpts(); roomSync(); chatterSchedule(); return; }
      if (sel && sel.dataset.sel === 'talk') { opts.talk = sel.value; opts.chatter = sel.value !== 'off'; saveOpts(); audioCtx(); chatterSchedule(); renderPlay(); return; }
      if (sel && sel.dataset.sel === 'assign') { opts.voiceAssign = opts.voiceAssign || {}; if (sel.value) opts.voiceAssign[sel.dataset.name] = sel.value; else delete opts.voiceAssign[sel.dataset.name]; saveOpts(); return; }
      const mv = pick(e, 'data-myvoice'); if (mv) { opts.myVoiceName = mv.dataset.myvoice; saveOpts(); return; }
      const b = pick(e, 'data-opt'); if (!b) return;
      opts[b.dataset.opt] = !!b.checked; saveOpts();
      if (b.dataset.opt === 'showBots') renderPlay();
      if (b.dataset.opt === 'pause' && !b.checked && g && !g.over) step();     // un-pausing lets the bots carry on
      if (b.dataset.opt === 'advise' || b.dataset.opt === 'pause' || b.dataset.opt === 'detail') renderPlay();
      if (b.dataset.opt === 'autoCalm') { if (auto) { auto.calm = !!b.checked; if (auto.calm) auto.speed = 'slow'; } renderPlay(); }
      if (b.dataset.opt === 'chatter' || b.dataset.opt === 'chatterQuiet' || b.dataset.opt === 'myTalk') { audioCtx(); chatterSchedule(); renderPlay(); }
      if (b.dataset.opt === 'roomTone') { audioCtx(); roomSync(); renderPlay(); }
      if (b.dataset.opt === 'voiceConsent') renderMain();
      if (b.dataset.opt === 'watch' || b.dataset.opt === 'stepBots') { renderPlay(); step(); }
      if (b.dataset.opt === 'speak') { if (opts.speak) { spokenLast = ''; said = new Set(); autoSpeak(); } else hush(); }
    };
    // F fold · C call/check · R raise (the recommended size) · H half pot · P pot · N next — when no box is being typed in
    document.addEventListener('keydown', (e) => {
      if (!shown || e.ctrlKey || e.metaKey || e.altKey) return;
      const t = e.target, typing = t && (/^(INPUT|TEXTAREA|SELECT)$/.test(t.tagName) || t.isContentEditable);
      if (typing) return;
      const k = e.key.toLowerCase(), m = $('trMain'); if (!m) return;
      const click = sel => { const b = m.querySelector(sel); if (b && !b.disabled) { e.preventDefault(); b.click(); return true; } return false; };
      if (k === 'f') click('[data-act="play:fold"], [data-act="pre:fold"], [data-act="ex:fold"], [data-act="pf:fold"], [data-act="icm:fold"]');
      else if (k === 'c') click('[data-act="play:call"], [data-act="play:check"], [data-act="pre:call"], [data-act="ex:call"], [data-act="ex:check"], [data-act="pf:call"], [data-act="icm:call"]');
      else if (k === 'r') click('[data-act="play:raise"], [data-act="pre:raise"], [data-act="ex:raise"], [data-act="pf:shove"], [data-act="icm:shove"]');
      else if (k === 'h') { const b = Array.from(m.querySelectorAll('[data-act="play:raise"]')).find(x => /^½ pot/.test(x.textContent)); if (b) { e.preventDefault(); b.click(); } }
      else if (k === 'p') { const b = Array.from(m.querySelectorAll('[data-act="play:raise"]')).find(x => /^Pot ·/.test(x.textContent)); if (b) { e.preventDefault(); b.click(); } }
      else if (k === 'n' || k === ' ') click('[data-act="play:continue"], [data-act="play:wnext"], [data-act="play:next"], [data-act="pre:next"], [data-act="pf:next"], [data-act="icm:next"], [data-act="odds:next"], [data-act="eq:next"], [data-act="outs:next"], [data-act="ex:next"], [data-act="hist:next"]');
    });
    $('trMain').onkeydown = (e) => {
      if (e.key !== 'Enter') return;
      const ids = { trOddsIn: 'odds', trEqIn: 'eq', trOutsIn: 'outs' }, ns = e.target && ids[e.target.id];
      if (ns) { e.preventDefault(); HANDLERS[ns]('check'); }
      if (e.target && e.target.id === 'trTo') { e.preventDefault(); HANDLERS.play('raiseTo'); }
      if (e.target && e.target.id === 'trCode') { e.preventDefault(); HANDLERS.room('join'); }
    };
  }

  // ⚙ Settings changed the voice: pick the new one up (app.js calls this when the dialog closes).
  function voiceChanged() { Promise.all([loadVoiceCfg(), loadLib()]).then(() => { if (HAS_LIB && !inbox) inboxOpen(); ttsFails = 0; stockVoices = null; chatterSchedule(); if (shown && tab === 'play') renderPlay(); }); }
  return {
    wire, open, close, voiceChanged, voiceLabel, sleepStory,
    _engine: { parseRange, chart, chartWidth, cls, pct, combos, tierOn, draws, handName, equityVsRanges, newGame, newHand, legal, act, settle, botDecide, preflopAdvice, gradePre, gradePost, spot, historyText, potTotal, posOf, newTournament, tourIcm, shortSpot, gradeShort, pfTable, mulberry, LESSON_HANDS, lessonGame, autoTo, bestKind, plain, detailFor, POS, bluffMoment, gearOf, forSpeech, storyHtml, levelWhy, COACH_LEVELS, rangeSetFor, tableLessonScore, FIELDS, whatIf, closeSitting, gradeShortCash, mulberry, setFieldForTest: v => { const p = opts.field; opts.field = v; return p; }, candidates, thresholds, pickBest, inPosition, primerHtml, HAND_RANKS, rankOf, adviceForSpot, gradeForSpot, recordCoached, levelWhyFor: levelWhy, REMARKS, pickRemark, INVITE, VOICE_PARA, VOICE_PARA2, TALK_LEVELS, TALK_SYSTEM, setLevelForTest: v => { opts.level = v; } },
  };
})();

if (typeof module !== 'undefined' && module.exports) module.exports = Trainer;
