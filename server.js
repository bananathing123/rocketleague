// Rocket League online relay server.
// Serves the game from /public and relays private-match traffic over WebSocket (/ws).
// The match HOST's browser runs the physics; this server just manages rooms and forwards messages.
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
let nextId = 1;

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

function leave(ws) {
  const room = ws.room;
  if (!room) return;
  ws.room = null;
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

const wss = new WebSocketServer({ server, path: '/ws', maxPayload: 64 * 1024 });

wss.on('connection', ws => {
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
        if (!room || room.host !== ws.pid || room.started) return;
        const p = room.players.get(m.id);
        const t = m.team === 1 ? 1 : 0;
        if (!p || p.team === t) return;
        if (teamCount(room, t) >= MAX_TEAM) return send(ws, { t: 'err', msg: 'That team is full (3 max).' });
        p.team = t;
        broadcastLobby(room);
        break;
      }
      case 'cfg': {
        if (!room || room.host !== ws.pid || room.started) return;
        const map = Math.max(0, Math.min(9, m.map | 0));
        room.map = map;
        room.len = [120, 180, 300].includes(m.len) ? m.len : 120;
        broadcastLobby(room);
        break;
      }
      case 'start': {
        if (!room || room.host !== ws.pid || room.started) return;
        room.started = true;
        const players = [...room.players.values()].map(p => ({ id: p.id, name: p.name, team: p.team }));
        for (const p of room.players.values())
          send(p.ws, { t: 'start', you: p.id, host: room.host, players, map: room.map, len: room.len });
        break;
      }
      case 'in': { // client -> host: controls
        if (!room || room.host === ws.pid || !Array.isArray(m.i)) return;
        const h = room.players.get(room.host);
        if (h) send(h.ws, { t: 'in', id: ws.pid, i: m.i.slice(0, 6) });
        break;
      }
      case 'snap': // host -> everyone else: world state
      case 'ev': { // host -> everyone else (or one player via m.to): one-off events
        if (!room || room.host !== ws.pid) return;
        const data = JSON.stringify(m);
        for (const p of room.players.values()) {
          if (p.id === ws.pid) continue;
          if (m.to && p.id !== m.to) continue;
          if (p.ws.readyState === 1) p.ws.send(data);
        }
        break;
      }
      case 'leave': leave(ws); break;
    }
  });

  ws.on('close', () => leave(ws));
  ws.on('error', () => {});
});

// keep connections alive through Render's proxy and drop dead sockets
setInterval(() => {
  for (const ws of wss.clients) {
    if (!ws.alive) { ws.terminate(); continue; }
    ws.alive = false;
    try { ws.ping(); } catch (e) {}
  }
}, 25000);

server.listen(PORT, () => console.log('Rocket League server listening on ' + PORT));
