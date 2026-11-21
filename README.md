# Rocket League – Online (Private Matches)

Your Phase 3 game plus **online private matches**.

## How it plays
- **PLAY → PRIVATE MATCH** opens a page with **JOIN MATCH** and **CREATE MATCH**.
- **Create** shows a lobby with a 4-letter code (e.g. `RUSH`). Share it. You pick the arena and match length,
  and use the arrow buttons next to each player to put them on **Blue** or **Orange** (3 per team, 6 players max).
  Press **START MATCH** when everyone is in.
- **Join** asks for the 4-letter code and drops you into that lobby.
- Everything else (controls, garage, boost pads, demos, replays, scoreboard with `Tab`) works as before.

## How it works
The **host's browser** runs the physics (the same code as offline play). Other players send their controls through
the server; the host streams the world state back ~30 times a second. The Node server only manages rooms and relays messages.

Because of that:
- Keep the **host's tab in the foreground** (browsers pause background tabs, which would freeze the match for everyone).
- Pick the player with the best connection/computer as host.
- Other players feel roughly their ping as input delay.

## Run locally
```
npm install
npm start
```
Open http://localhost:3000 (open it in two tabs to test a match).

## Deploy on Render
1. Push this folder to a GitHub repo.
2. On https://render.com: **New → Web Service** → pick the repo.
   (Or **New → Blueprint** – `render.yaml` is included and fills everything in.)
3. Settings if asked: Runtime **Node**, Build Command `npm install`, Start Command `node server.js`.
4. Deploy, then open your `https://<name>.onrender.com` link and share it with friends.

Free-tier note: Render free services sleep after ~15 min idle, so the first load can take ~30–60 s. Matches in progress keep the server awake.
