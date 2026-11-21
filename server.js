// Rocket League online relay server.
// Serves the game from /public and relays private-match traffic over WebSocket (/ws).
// The match HOST's browser runs the physics; this server just manages rooms and forwards messages.
// It also does matchmaking for Casual / Competitive duels: players queue ('mm'), get paired by MMR
// (the allowed gap widens the longer they wait), and are put into a private 1v1 room automatically.
const http = require('http');
const fs = require('fs');
const path = require('path');
const { WebSocketServer } = require('ws');

const PORT = process.env.PORT || 3000;
const PUB = path.join(__dirname, 'public');
const MIME = {
  '.html': 'text/html; charset=utf-8', '.js': 'text/javascript', '.css': 'text/css',
  '.png': 'image/png', '.ico': 'image/x-icon', '.json': 'application/json', '.svg': 'image/svg+xml'
};

const server = http.createServer((req, res) => {
  const u = decodeURIComponent(req.url.split('?')[0]);
  if (u === '/healthz') { res.writeHead(200); res.end('ok'); return; }
  const f = u === '/' ? '/index.html' : u;
  const fp = path.normalize(path.join(PUB, f));
  if (!fp.startsWith(PUB)) { res.writeHead(403); res.end(); return; }
  fs.readFile(fp, (err, data) => {
    if (err) { res.writeHead(404); res.end('Not found'); return; }
    res.writeHead(200, {
      'Content-Type': MIME[path.extname(fp)] || 'application/octet-stream',
      'Cache-Control': 'no-cache'
    });
    res.end(data);
  });
});

const WORDS = ['GOAL','BALL','BOLT','BOOM','CARS','DASH','DOME','DUNK','FAST','FIRE','FLIP','FLUX','GAME','GEAR','GLOW','HERO','JUMP','KICK','LAPS','LEAP','LION','LUCK','MAZE','MOON','NOVA','OPEN','PACE','PUCK','RACE','RAMP','RING','ROAD','ROCK','SAVE','SHOT','SIDE','SLAM','SNOW','SPIN','STAR','SURF','TEAM','TIDE','TURF','TURN','VOLT','WAVE','WILD','WIND','WING','ZONE','ZOOM','ACES','AXLE','BASH','BEAM','BLUE','CAGE','CHIP','COIN','CREW','DARE','DAWN','DUSK','EDGE','EPIC','FANG','FLAG','FOAM','FORM','GALE','GRIP','GUST','HAZE','HOOK','IRON','JADE','JAZZ','KING','LAVA','LEAD','LINK','LOOP','MARS','MINT','NEON','NEXT','ONYX','PEAK','PINE','PLAY','PUSH','QUAD','RAIN','RUSH','SAND','SKID','SOAR','SPAR','TANK','TRIM','TUBE','UNIT','VIBE','VOID','WARP','WOLF','YARD','ZEAL','ZINC'];

const MAX_PLAYERS = 6, MAX_TEAM = 3;
const rooms = new Map(); // code -> room
// ---- matchmaking ----
const MM_MAPS = 5, MM_LEN = 120, MM_COUNTDOWN_MS = 3300;
const queues = { cas: [], comp: [] }; // kind -> [{ ws, name, mmr, since, kind }]
const mmWindow = (kind, waitSec) => (kind === 'comp' ? 150 + 60 * waitSec : 1000 + 200 * waitSec);
let nextId = 1;
// ---- friends / presence / parties ----
// Friend IDs are random friend codes (XXXX-XXXX). Each client opens one presence socket ('fr_hello') carrying its code, a secret token,
// its name, friend list, status and cosmetics. A friend's name and activity are only revealed when BOTH players have added each other.
// The first token to claim a code owns it (kept in memory; resets if the server restarts).
const frInfo = new Map();  // code -> { name, friends:Set, st, cos }   (last known, kept after disconnect so offline friends keep their names)
const frSocks = new Map(); // code -> Set(ws) of connected presence sockets
const frTok = new Map();   // code -> secret token
const parties = new Map(); // id -> { id, leader, members:[codes], invites:Map(code->expiry ms), room }
const partyOf = new Map(); // code -> party id
const PARTY_MAX = 6, INVITE_MS = 60000;
let frDirty = false;
const CODE_RE = /^[A-HJ-NP-Z2-9]{4}-[A-HJ-NP-Z2-9]{4}$/;
const normCode = s => { const t = String(s || '').toUpperCase().replace(/[^A-Z0-9]/g, ''); return t.length === 8 ? t.slice(0, 4) + '-' + t.slice(4) : ''; };
const validCode = s => CODE_RE.test(s);
const cleanSt = s => String(s || 'Main Menu').replace(/[^A-Za-z: ]/g, '').slice(0, 24) || 'Main Menu';
const cleanCos = o => { const r = {}; for (const k of ['body', 'decal', 'dcol', 'wheel', 'boost', 'top', 'expl']) r[k] = Math.max(-1, Math.min(9, ((o && o[k]) | 0))); return r; };
const socksOf = code => [...(frSocks.get(code) || [])];
const sendCode = (code, o) => { for (const w of socksOf(code)) send(w, o); };
function ptDisband(p) { for (const c of p.members) partyOf.delete(c); parties.delete(p.id); frDirty = true; }
function ptLeave(code) {
  const id = partyOf.get(code); if (!id) return;
  partyOf.delete(code);
  const p = parties.get(id); if (!p) return;
  p.members = p.members.filter(c => c !== code);
  if (p.leader === code) { p.leader = p.members[0]; p.room = null; }
  if (!p.members.length || (p.members.length === 1 && !p.invites.size)) ptDisband(p);
  frDirty = true;
}
function ptView(code) {
  const p = parties.get(partyOf.get(code)); if (!p) return null;
  return { id: p.id, leader: p.leader, members: p.members.map(c => { const i = frInfo.get(c) || {}; return { code: c, name: i.name || '?', cos: i.cos || {}, st: i.st || 'Main Menu' }; }) };
}
function frRemove(ws) {
  if (!ws.fr) return;
  ws.fr = false;
  const set = frSocks.get(ws.code);
  if (set) { set.delete(ws); if (!set.size) { frSocks.delete(ws.code); ptLeave(ws.code); } }
  frDirty = true;
}
function frView(ws) {
  const me = ws.code;
  const list = [...ws.frFriends].map(code => {
    const inf = frInfo.get(code), mutual = !!inf && inf.friends.has(me), on = mutual && frSocks.has(code);
    return mutual ? { code, mutual: true, online: on, name: inf.name, st: on ? inf.st : undefined } : { code, mutual: false, online: false };
  });
  return { t: 'fr', you: me, list, party: ptView(me) };
}
function frFlush() {
  const now = Date.now();
  for (const p of [...parties.values()]) {
    for (const [c, exp] of p.invites) if (exp < now) { p.invites.delete(c); frDirty = true; }
    if (p.members.length === 1 && !p.invites.size) ptDisband(p);
  }
  if (!frDirty) return;
  frDirty = false;
  for (const set of frSocks.values()) for (const ws of set) {
    const j = JSON.stringify(frView(ws));
    if (j !== ws.frLast) { ws.frLast = j; if (ws.readyState === 1) ws.send(j); }
  }
}

function genCode() {
  for (let i = 0; i < 60; i++) {
    const w = WORDS[Math.floor(Math.random() * WORDS.length)];
    if (!rooms.has(w)) return w;
  }
  const L = 'ABCDEFGHJKLMNPQRSTUVWXYZ';
  for (;;) {
    let c = '';
    for (let i = 0; i < 4; i++) c += L[Math.floor(Math.random() * L.length)];
    if (!rooms.has(c)) return c;
  }
}

const cleanName = n => String(n || 'PLAYER').replace(/[<>&"'`\\]/g, '').trim().slice(0, 16) || 'PLAYER';
const send = (ws, o) => { if (ws && ws.readyState === 1) ws.send(JSON.stringify(o)); };
const teamCount = (room, t) => [...room.players.values()].filter(p => p.team === t).length;

function lobbyFor(room, ws) {
  return {
    t: 'lobby', code: room.code, host: room.host, you: ws.pid, map: room.map, len: room.len,
    players: [...room.players.values()].map(p => ({ id: p.id, name: p.name, team: p.team }))
  };
}
function broadcastLobby(room) {
  for (const p of room.players.values()) send(p.ws, lobbyFor(room, p.ws));
}

function dequeue(ws) {
  for (const k of Object.keys(queues)) {
    const i = queues[k].findIndex(e => e.ws === ws);
    if (i >= 0) queues[k].splice(i, 1);
  }
}

function enqueue(entry) {
  if (entry.ws.readyState !== 1) return;
  queues[entry.kind].push(entry);
  tryMatch(entry.kind);
  sendQueueCounts();
}

function sendQueueCounts() {
  for (const k of Object.keys(queues))
    for (const e of queues[k]) send(e.ws, { t: 'mmq', n: queues[k].length });
}

function startMsgs(room) {
  const players = [...room.players.values()].map(p => ({ id: p.id, name: p.name, team: p.team }));
  for (const p of room.players.values())
    send(p.ws, { t: 'start', you: p.id, host: room.host, players, map: room.map, len: room.len });
}

function makeMatch(a, b, kind) {
  const code = genCode();
  const r = {
    code, host: a.ws.pid, players: new Map(), map: Math.floor(Math.random() * MM_MAPS), len: MM_LEN,
    started: true, mm: true, ranked: kind === 'comp', pending: true, over: false, entries: new Map(), timer: null
  };
  [a, b].forEach((e, team) => {
    r.players.set(e.ws.pid, { id: e.ws.pid, name: e.name, team, ws: e.ws });
    r.entries.set(e.ws.pid, e);
    e.ws.room = r;
  });
  rooms.set(code, r);
  send(a.ws, { t: 'mmf', k: kind, map: r.map, len: r.len, opp: { name: b.name, mmr: b.mmr } });
  send(b.ws, { t: 'mmf', k: kind, map: r.map, len: r.len, opp: { name: a.name, mmr: a.mmr } });
  // give both clients time to show their 3-2-1 before the match really starts
  r.timer = setTimeout(() => {
    r.timer = null;
    r.pending = false;
    if ([...r.players.values()].every(p => p.ws.readyState === 1)) startMsgs(r);
  }, MM_COUNTDOWN_MS);
}

function tryMatch(kind) {
  const q = queues[kind];
  const now = Date.now();
  q.sort((x, y) => x.since - y.since); // longest-waiting first
  for (let i = 0; i < q.length; i++) {
    const a = q[i];
    let best = -1, bestGap = Infinity;
    for (let j = 0; j < q.length; j++) {
      if (j === i) continue;
      const b = q[j], gap = Math.abs(a.mmr - b.mmr);
      const wait = Math.max(now - a.since, now - b.since) / 1000;
      if (gap <= mmWindow(kind, wait) && gap < bestGap) { best = j; bestGap = gap; }
    }
    if (best >= 0) {
      const b = q[best];
      q.splice(Math.max(i, best), 1);
      q.splice(Math.min(i, best), 1);
      makeMatch(a, b, kind);
      return tryMatch(kind); // maybe more pairs
    }
  }
}

function leave(ws) {
  dequeue(ws);
  const room = ws.room;
  if (!room) return;
  ws.room = null;
  if (room.mm) {
    room.players.delete(ws.pid);
    const rest = [...room.players.values()];
    for (const p of rest) p.ws.room = null;
    rooms.delete(room.code);
    if (room.pending) {
      // someone left during the countdown: cancel the match and put the other player back in the queue
      if (room.timer) { clearTimeout(room.timer); room.timer = null; }
      for (const p of rest) {
        send(p.ws, { t: 'mmx' });
        const e = room.entries.get(p.id);
        if (e) enqueue(e);
      }
    } else if (!room.over) {
      // someone left mid-match: the other player wins by forfeit
      for (const p of rest) send(p.ws, { t: 'mmwin' });
    }
    return;
  }
  room.players.delete(ws.pid);
  if (room.host === ws.pid) {
    for (const p of room.players.values()) { send(p.ws, { t: 'closed' }); p.ws.room = null; }
    rooms.delete(room.code);
  } else if (room.players.size === 0) {
    rooms.delete(room.code);
  } else {
    broadcastLobby(room);
  }
}

const wss = new WebSocketServer({ server, path: '/ws', maxPayload: 64 * 1024, perMessageDeflate: false });

wss.on('connection', (ws, req) => {
  ws.pid = nextId++;
  ws.room = null;
  ws.alive = true;
  ws.on('pong', () => { ws.alive = true; });

  ws.on('message', raw => {
    let m;
    try { m = JSON.parse(raw); } catch (e) { return; }
    if (!m || typeof m.t !== 'string') return;
    const room = ws.room;

    switch (m.t) {
      case 'create': {
        if (room) leave(ws);
        const code = genCode();
        const r = { code, host: ws.pid, players: new Map(), map: 0, len: 120, started: false };
        r.players.set(ws.pid, { id: ws.pid, name: cleanName(m.name), team: 0, ws });
        rooms.set(code, r);
        ws.room = r;
        broadcastLobby(r);
        break;
      }
      case 'join': {
        if (room) leave(ws);
        const code = String(m.code || '').toUpperCase().replace(/[^A-Z]/g, '').slice(0, 4);
        const r = rooms.get(code);
        if (!r) return send(ws, { t: 'err', msg: 'No match found with that code.' });
        if (r.started) return send(ws, { t: 'err', msg: 'That match has already started.' });
        if (r.players.size >= MAX_PLAYERS) return send(ws, { t: 'err', msg: 'That match is full.' });
        const team = teamCount(r, 0) <= teamCount(r, 1) ? 0 : 1;
        r.players.set(ws.pid, { id: ws.pid, name: cleanName(m.name), team, ws });
        ws.room = r;
        broadcastLobby(r);
        break;
      }
      case 'team': {
        if (!room || room.mm || room.host !== ws.pid || room.started) return;
        const p = room.players.get(m.id);
        const t = m.team === 1 ? 1 : 0;
        if (!p || p.team === t) return;
        if (teamCount(room, t) >= MAX_TEAM) return send(ws, { t: 'err', msg: 'That team is full (3 max).' });
        p.team = t;
        broadcastLobby(room);
        break;
      }
      case 'cfg': {
        if (!room || room.mm || room.host !== ws.pid || room.started) return;
        const map = Math.max(0, Math.min(9, m.map | 0));
        room.map = map;
        room.len = [120, 180, 300].includes(m.len) ? m.len : 120;
        broadcastLobby(room);
        break;
      }
      case 'start': {
        if (!room || room.mm || room.host !== ws.pid || room.started) return;
        room.started = true;
        startMsgs(room);
        break;
      }
      case 'in': { // client -> host: controls
        if (!room || room.host === ws.pid || !Array.isArray(m.i)) return;
        const h = room.players.get(room.host);
        if (h) send(h.ws, { t: 'in', id: ws.pid, i: m.i.slice(0, 6) });
        break;
      }
      case 'sig': { // WebRTC introductions: forward to one player in the same room
        if (!room || !m.d) return;
        const tgt = room.players.get(m.to);
        if (tgt) send(tgt.ws, { t: 'sig', from: ws.pid, d: m.d });
        break;
      }
      case 'mm': { // join the matchmaking queue
        if (room) leave(ws);
        dequeue(ws);
        const kind = m.k === 'comp' ? 'comp' : 'cas';
        const mmr = Math.max(0, Math.min(5000, Number(m.mmr) | 0));
        enqueue({ ws, name: cleanName(m.name), mmr, since: Date.now(), kind });
        break;
      }
      case 'mmc': dequeue(ws); break; // cancel search
      case 'over': if (room && room.mm) room.over = true; break; // the client has seen the final whistle
      case 'chat': { // in-match text chat: relayed to everyone in the room, with the name taken from the server's record
        if (!room) return;
        const me = room.players.get(ws.pid);
        if (!me) return;
        const now = Date.now();
        ws.chatT = (ws.chatT || []).filter(x => now - x < 5000);
        if (ws.chatT.length >= 5) return; // max 5 messages per 5 seconds
        const msg = String(m.m || '').replace(/[\u0000-\u001f\u007f]/g, '').replace(/\s+/g, ' ').trim().slice(0, 100);
        if (!msg) return;
        ws.chatT.push(now);
        const data = JSON.stringify({ t: 'chat', id: ws.pid, name: me.name, team: me.team, msg });
        for (const p of room.players.values()) if (p.ws.readyState === 1) p.ws.send(data);
        break;
      }
      case 'fr_hello': { // presence + friend list (re-sent whenever name / status / cosmetics / friend list changes)
        const code = normCode(m.code), tok = String(m.tok || '');
        if (!validCode(code) || tok.length < 16 || tok.length > 64) return send(ws, { t: 'fr_err', why: 'bad' });
        const have = frTok.get(code);
        if (have && have !== tok) return send(ws, { t: 'fr_err', why: 'taken' });
        if (!have) frTok.set(code, tok);
        if (ws.fr && ws.code !== code) frRemove(ws);
        ws.code = code;
        const friends = (Array.isArray(m.friends) ? m.friends : []).slice(0, 100).map(normCode).filter(x => validCode(x) && x !== code);
        ws.frName = cleanName(m.name); ws.frFriends = new Set(friends);
        if (!ws.fr) { ws.fr = true; if (!frSocks.has(code)) frSocks.set(code, new Set()); frSocks.get(code).add(ws); }
        frInfo.set(code, { name: ws.frName, friends: ws.frFriends, st: cleanSt(m.st), cos: cleanCos(m.cos) });
        frDirty = true;
        break;
      }
      case 'pt_inv': { // party leader (or anyone not in a party) invites a mutual, online friend
        if (!ws.fr) return;
        const to = normCode(m.to), inf = frInfo.get(to);
        if (!inf || !ws.frFriends.has(to) || !inf.friends.has(ws.code) || !frSocks.has(to)) return send(ws, { t: 'pt_err', msg: 'That friend is not online.' });
        let p = parties.get(partyOf.get(ws.code));
        if (p && p.leader !== ws.code) return send(ws, { t: 'pt_err', msg: 'Only the party leader can invite.' });
        if (p && p.members.includes(to)) return;
        if (p && p.members.length >= PARTY_MAX) return send(ws, { t: 'pt_err', msg: 'Your party is full (6 max).' });
        if (partyOf.has(to)) return send(ws, { t: 'pt_err', msg: 'That player is already in a party.' });
        if (!p) { p = { id: 'P' + (nextId++), leader: ws.code, members: [ws.code], invites: new Map(), room: null }; parties.set(p.id, p); partyOf.set(ws.code, p.id); }
        p.invites.set(to, Date.now() + INVITE_MS);
        sendCode(to, { t: 'pt_invite', pid: p.id, from: ws.code, name: ws.frName });
        frDirty = true;
        break;
      }
      case 'pt_acc': {
        if (!ws.fr) return;
        const p = parties.get(String(m.pid)), exp = p && p.invites.get(ws.code);
        if (!p || !exp || exp < Date.now()) return send(ws, { t: 'pt_err', msg: 'That party invite has expired.' });
        if (p.members.length >= PARTY_MAX) return send(ws, { t: 'pt_err', msg: 'That party is full.' });
        p.invites.delete(ws.code);
        if (partyOf.has(ws.code)) ptLeave(ws.code);
        if (!parties.has(p.id)) return send(ws, { t: 'pt_err', msg: 'That party no longer exists.' });
        p.members.push(ws.code); partyOf.set(ws.code, p.id);
        frDirty = true;
        if (p.room) { const l = socksOf(ws.code).pop(); if (l) send(l, { t: 'pt_join', code: p.room }); } // leader already opened a private lobby
        break;
      }
      case 'pt_dec': {
        const p = parties.get(String(m.pid));
        if (p && p.invites.delete(ws.code)) { sendCode(p.leader, { t: 'pt_note', msg: ws.frName + ' declined your party invite.' }); frDirty = true; }
        break;
      }
      case 'pt_leave': if (ws.fr) ptLeave(ws.code); break;
      case 'pt_kick': {
        if (!ws.fr) return;
        const p = parties.get(partyOf.get(ws.code)), t = normCode(m.code);
        if (!p || p.leader !== ws.code || t === ws.code || !p.members.includes(t)) return;
        ptLeave(t);
        sendCode(t, { t: 'pt_note', msg: 'You were removed from the party.' });
        break;
      }
      case 'pt_go': { // leader opened (or closed) a private lobby: everyone else in the party joins it
        if (!ws.fr) return;
        const p = parties.get(partyOf.get(ws.code));
        if (!p || p.leader !== ws.code) return;
        const rc = m.code ? String(m.code).toUpperCase().replace(/[^A-Z]/g, '').slice(0, 4) : null;
        p.room = rc && rc.length === 4 ? rc : null;
        if (p.room) for (const c of p.members) if (c !== ws.code) { const l = socksOf(c).pop(); if (l) send(l, { t: 'pt_join', code: p.room }); }
        break;
      }
      case 'pg': send(ws, { t: 'pg', c: m.c }); break; // ping echo (clients use it to measure latency)
      case 'snap': { // host -> everyone else: world state, relayed as-is (no re-encoding)
        if (!room || room.host !== ws.pid) return;
        for (const p of room.players.values()) {
          if (p.id === ws.pid || p.ws.readyState !== 1) continue;
          if (Array.isArray(m.o) && !m.o.includes(p.id)) continue; // already got it over a direct link
          if (p.ws.bufferedAmount > 32768) continue; // slow client: drop stale snapshots instead of queueing lag
          p.ws.send(raw, { binary: false });
        }
        break;
      }
      case 'ev': { // host -> everyone else (or one player via m.to): one-off events
        if (!room || room.host !== ws.pid) return;
        const data = JSON.stringify(m);
        for (const p of room.players.values()) {
          if (p.id === ws.pid) continue;
          if (m.to && p.id !== m.to) continue;
          if (Array.isArray(m.o) && !m.o.includes(p.id)) continue;
          if (p.ws.readyState === 1) p.ws.send(data);
        }
        break;
      }
      case 'leave': leave(ws); break;
    }
  });

  ws.on('close', () => { leave(ws); frRemove(ws); });
  ws.on('error', () => {});
});

// keep connections alive through Render's proxy and drop dead sockets
// matchmaking tick: widen the MMR window as people wait, and tell searchers how many are in the queue
setInterval(frFlush, 700);
setInterval(() => { tryMatch('cas'); tryMatch('comp'); sendQueueCounts(); }, 1000);

setInterval(() => {
  for (const ws of wss.clients) {
    if (!ws.alive) { ws.terminate(); continue; }
    ws.alive = false;
    try { ws.ping(); } catch (e) {}
  }
}, 25000);

server.listen(PORT, () => console.log('Rocket League server listening on ' + PORT));
