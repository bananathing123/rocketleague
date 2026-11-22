// Rocket League online server.
// Serves the game from /public and runs every online match over WebSocket (/ws).
// THIS SERVER IS THE HOST: it runs the physics / bots / scoring for every match (see sim.js) and streams the world to the players.
// Players only send their controls and render what the server sends (their own car is predicted locally so it still feels instant).
// Private matches: up to 8 players (4 per team) and bots can be added to either team by the lobby leader.
// It also does matchmaking for Casual / Competitive duels: players queue ('mm'), get paired by MMR
// (the allowed gap widens the longer they wait), and are put into a private 1v1 room automatically.
const http = require('http');
const fs = require('fs');
const path = require('path');
const { WebSocketServer } = require('ws');
const { makeSim } = require('./sim');

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

const MAX_PLAYERS = 8, MAX_TEAM = 4;   // humans + bots together
const TICK_HZ = 60, SNAP_HZ = Math.max(20, Math.min(60, +process.env.SNAP_HZ || 60));   // physics rate / how often the world is sent to players
const BOT_NAMES = ['Wisp','Nova','Hunter','Dash','Rex','Blaze','Tank','Echo','Viper','Dozer','Zap','Fuzz'];
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
const PARTY_MAX = 8, INVITE_MS = 60000;
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
const botsOf = room => room.bots || (room.bots = []);
const teamCount = (room, t) => [...room.players.values()].filter(p => p.team === t).length + botsOf(room).filter(p => p.team === t).length;
const totalCount = room => room.players.size + botsOf(room).length;
let nextBotId = 1;
function freeBotName(room) {
  const used = new Set([...botsOf(room).map(b => b.name), ...[...room.players.values()].map(p => p.name)]);
  const start = Math.floor(Math.random() * BOT_NAMES.length);
  for (let i = 0; i < BOT_NAMES.length; i++) { const n = BOT_NAMES[(start + i) % BOT_NAMES.length]; if (!used.has(n)) return n; }
  return 'Bot' + botsOf(room).length;
}
const allPlayers = room => [...room.players.values()].map(p => ({ id: p.id, name: p.name, team: p.team }))
  .concat(botsOf(room).map(b => ({ id: b.id, name: b.name, team: b.team, bot: 1 })));

function lobbyFor(room, ws) {
  return {
    t: 'lobby', code: room.code, host: room.host, you: ws.pid, map: room.map, len: room.len, diff: room.diff == null ? 1 : room.diff,
    players: allPlayers(room)
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
  const players = allPlayers(room);
  for (const p of room.players.values())
    send(p.ws, { t: 'start', you: p.id, host: room.host, players, map: room.map, len: room.len });
  startSim(room, players);
}

// ---- the server-side match: one sim per started room, stepped at a fixed rate and streamed to the players ----
const simRooms = new Set();
function startSim(room, players) {
  stopSim(room);
  room.sim = makeSim();
  room.sim.start(players, { len: room.len, diff: room.diff == null ? 1 : room.diff });
  room.simAcc = 0; room.simLast = process.hrtime.bigint(); room.snapT = 0;
  simRooms.add(room);
}
function stopSim(room) { if (room.sim) { simRooms.delete(room); room.sim = null; } }
function flushEvents(room) {
  const list = room.sim.drainEv();
  if (!list.length) return;
  const all = list.filter(x => x.to == null).map(x => x.e);
  if (all.length) {
    const data = JSON.stringify({ t: 'ev', e: all });
    for (const p of room.players.values()) if (p.ws.readyState === 1) p.ws.send(data);
  }
  for (const x of list) if (x.to != null) { const p = room.players.get(x.to); if (p) send(p.ws, { t: 'ev', e: [x.e] }); }
}
function simLoop() {
  const now = process.hrtime.bigint();
  for (const room of [...simRooms]) {
    const sim = room.sim; if (!sim) continue;
    room.simAcc += Number(now - room.simLast) / 1e9; room.simLast = now;
    if (room.simAcc > .25) room.simAcc = .25;   // never try to catch up a huge stall
    const dt = 1 / TICK_HZ;
    while (room.simAcc >= dt) {
      room.simAcc -= dt;
      try { sim.tick(dt); } catch (e) {   // a bug in one match must never take the whole server down
        console.error('sim error in room', room.code, e);
        for (const p of room.players.values()) { send(p.ws, { t: 'closed' }); p.ws.room = null; }
        rooms.delete(room.code); stopSim(room); break;
      }
      room.snapT += dt;
      if (room.snapT >= 1 / SNAP_HZ - 1e-4) {
        room.snapT = 0;
        flushEvents(room);
        const data = JSON.stringify(sim.snapshot());
        for (const p of room.players.values()) {
          if (p.ws.readyState !== 1) continue;
          if (p.ws.bufferedAmount > 32768) continue;   // slow client: drop a stale snapshot instead of queueing lag
          p.ws.send(data);
        }
      }
    }
  }
}
setInterval(simLoop, 1000 / TICK_HZ / 2);

function makeMatch(a, b, kind) {
  const code = genCode();
  const r = {
    code, host: a.ws.pid, players: new Map(), map: Math.floor(Math.random() * MM_MAPS), len: MM_LEN,
    started: true, mm: true, ranked: kind === 'comp', pending: true, over: false, entries: new Map(), timer: null, bots: [], diff: 1
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
    stopSim(room);
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
  if (room.sim) room.sim.removeCar(ws.pid);
  if (room.players.size === 0) {   // nobody left: the match is over, the server stops simulating it
    stopSim(room);
    rooms.delete(room.code);
    return;
  }
  if (room.host === ws.pid) room.host = [...room.players.keys()][0];   // the match keeps running on the server; leadership moves to the next player
  broadcastLobby(room);
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
        const r = { code, host: ws.pid, players: new Map(), map: 0, len: 120, started: false, bots: [], diff: 1 };
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
        if (totalCount(r) >= MAX_PLAYERS && botsOf(r).length) botsOf(r).pop();   // a full lobby makes room for a real player by dropping the newest bot
        if (totalCount(r) >= MAX_PLAYERS) return send(ws, { t: 'err', msg: 'That match is full.' });
        const team = teamCount(r, 0) <= teamCount(r, 1) ? 0 : 1;
        r.players.set(ws.pid, { id: ws.pid, name: cleanName(m.name), team, ws });
        ws.room = r;
        broadcastLobby(r);
        break;
      }
      case 'team': {
        if (!room || room.mm || room.host !== ws.pid || room.started) return;
        const p = room.players.get(m.id) || botsOf(room).find(b => b.id === m.id);
        const t = m.team === 1 ? 1 : 0;
        if (!p || p.team === t) return;
        if (teamCount(room, t) >= MAX_TEAM) return send(ws, { t: 'err', msg: 'That team is full (4 max).' });
        p.team = t;
        broadcastLobby(room);
        break;
      }
      case 'cfg': {
        if (!room || room.mm || room.host !== ws.pid || room.started) return;
        const map = Math.max(0, Math.min(9, m.map | 0));
        room.map = map;
        room.len = [120, 180, 300].includes(m.len) ? m.len : 120;
        if (m.diff != null) room.diff = Math.max(0, Math.min(2, m.diff | 0));
        broadcastLobby(room);
        break;
      }
      case 'addbot': { // lobby leader adds a bot to any team
        if (!room || room.mm || room.host !== ws.pid || room.started) return;
        const t = m.team === 1 ? 1 : 0;
        if (totalCount(room) >= MAX_PLAYERS) return send(ws, { t: 'err', msg: 'The match is full (8 max).' });
        if (teamCount(room, t) >= MAX_TEAM) return send(ws, { t: 'err', msg: 'That team is full (4 max).' });
        botsOf(room).push({ id: -(nextBotId++), name: freeBotName(room), team: t });
        broadcastLobby(room);
        break;
      }
      case 'rmbot': {
        if (!room || room.mm || room.host !== ws.pid || room.started) return;
        const i = botsOf(room).findIndex(b => b.id === m.id);
        if (i >= 0) { botsOf(room).splice(i, 1); broadcastLobby(room); }
        break;
      }
      case 'rematch': { // the leader plays again on the same server-side match
        if (!room || room.mm || room.host !== ws.pid || !room.sim || !room.sim.matchEnd) return;
        room.sim.rematch();
        break;
      }
      case 'start': {
        if (!room || room.mm || room.host !== ws.pid || room.started) return;
        room.started = true;
        startMsgs(room);
        break;
      }
      case 'in': { // controls go straight into the server-side match
        if (!room || !room.sim || !Array.isArray(m.i)) return;
        room.sim.input(ws.pid, m.i.slice(0, 6));
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
        if (p && p.members.length >= PARTY_MAX) return send(ws, { t: 'pt_err', msg: 'Your party is full (8 max).' });
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

server.listen(PORT, () => console.log('Rocket League server (hosts every match itself) listening on ' + PORT));
