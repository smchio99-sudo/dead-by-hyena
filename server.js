'use strict';
const http = require('http');
const fs = require('fs');
const path = require('path');
const { WebSocketServer, WebSocket } = require('ws');

const PORT = process.env.PORT || 3000;

// ── HTTP server (serves static files) ──────────────────────────────────────
const httpServer = http.createServer((req, res) => {
  let filePath = path.join(__dirname, 'public', req.url === '/' ? 'index.html' : req.url);
  const ext = path.extname(filePath);
  const mime = { '.html':'text/html', '.js':'application/javascript', '.css':'text/css', '.mp4':'video/mp4' };
  fs.readFile(filePath, (err, data) => {
    if (err) { res.writeHead(404); res.end('Not found'); return; }
    res.writeHead(200, { 'Content-Type': mime[ext] || 'application/octet-stream' });
    res.end(data);
  });
});

// ── Game constants (mirrored from client) ──────────────────────────────────
const WORLD_WIDTH = 3000;
const WORLD_HEIGHT = 3000;
const CAMERA_ZOOM = 1.28;
const CENTER_CORRIDOR_HALF = 145;
const PLAYER_SAFE_RADIUS = 240;
const KILLER_SAFE_RADIUS = 240;
const GENERATOR_WORKSPACE = 120;
const LOCKER_MIN_DISTANCE = 210;
const PLAYER_START_1 = { x: 1500, y: 1400 };
const PLAYER_START_2 = { x: 1600, y: 1600 };
const KILLER_START = { x: 430, y: 430 };

// ── World generation (server-authoritative) ────────────────────────────────
function clamp(v, min, max) { return Math.max(min, Math.min(max, v)); }
function rectsOverlap(a, b, margin = 0) {
  return !(a.x+a.w+margin < b.x || b.x+b.w+margin < a.x || a.y+a.h+margin < b.y || b.y+b.h+margin < a.y);
}
function pointInRect(px, py, rect, margin = 0) {
  return px >= rect.x-margin && px <= rect.x+rect.w+margin && py >= rect.y-margin && py <= rect.y+rect.h+margin;
}
function circleRectOverlap(cx, cy, r, rect, margin = 0) {
  const nx = clamp(cx, rect.x-margin, rect.x+rect.w+margin);
  const ny = clamp(cy, rect.y-margin, rect.y+rect.h+margin);
  return ((cx-nx)**2+(cy-ny)**2) <= r**2;
}
function structureBBox(segments) {
  const minX = Math.min(...segments.map(s=>s.x));
  const minY = Math.min(...segments.map(s=>s.y));
  const maxX = Math.max(...segments.map(s=>s.x+s.w));
  const maxY = Math.max(...segments.map(s=>s.y+s.h));
  return { x:minX, y:minY, w:maxX-minX, h:maxY-minY };
}
function buildLStructure(x, y, size, arm, orientation) {
  const t = 28, segs = [];
  if(orientation===0){ segs.push({x,y,w:arm,h:t}); segs.push({x,y,w:t,h:size}); }
  else if(orientation===1){ segs.push({x:x+size-arm,y,w:arm,h:t}); segs.push({x:x+size-t,y,w:t,h:size}); }
  else if(orientation===2){ segs.push({x,y:y+size-t,w:arm,h:t}); segs.push({x,y,w:t,h:size}); }
  else { segs.push({x:x+size-arm,y:y+size-t,w:arm,h:t}); segs.push({x:x+size-t,y,w:t,h:size}); }
  return { kind:orientation%2===0?'ㄱ':'ㄴ', bbox:structureBBox(segs), segments:segs };
}
function buildDStructure(x, y, w, h, orientation) {
  const t=28, segs=[], inset=72;
  let vault;
  if(orientation===0){ segs.push({x,y,w,h:t}); segs.push({x,y,w:t,h}); segs.push({x:x+w-t,y,w:t,h}); vault={orientation:'horizontal',x1:x+inset,y1:y+t/2,x2:x+w-inset,y2:y+t/2}; }
  else if(orientation===1){ segs.push({x,y:y+h-t,w,h:t}); segs.push({x,y,w:t,h}); segs.push({x:x+w-t,y,w:t,h}); vault={orientation:'horizontal',x1:x+inset,y1:y+h-t/2,x2:x+w-inset,y2:y+h-t/2}; }
  else if(orientation===2){ segs.push({x,y,w:t,h}); segs.push({x,y,w,h:t}); segs.push({x,y:y+h-t,w,h:t}); vault={orientation:'vertical',x1:x+t/2,y1:y+inset,x2:x+t/2,y2:y+h-inset}; }
  else { segs.push({x:x+w-t,y,w:t,h}); segs.push({x,y,w,h:t}); segs.push({x,y:y+h-t,w,h:t}); vault={orientation:'vertical',x1:x+w-t/2,y1:y+inset,x2:x+w-t/2,y2:y+h-inset}; }
  vault.cx=(vault.x1+vault.x2)/2; vault.cy=(vault.y1+vault.y2)/2;
  vault.length=Math.hypot(vault.x2-vault.x1,vault.y2-vault.y1);
  return { kind:'ㄷ', bbox:structureBBox(segs), segments:segs, vault };
}
function buildLineVaultStructure(x, y, horizontal=true) {
  const thickness=28, length=Math.random()*180+260;
  const seg = horizontal?{x,y,w:length,h:thickness}:{x,y,w:thickness,h:length};
  const inset=68;
  const vault = horizontal
    ?{orientation:'horizontal',x1:x+inset,y1:y+thickness/2,x2:x+length-inset,y2:y+thickness/2}
    :{orientation:'vertical',x1:x+thickness/2,y1:y+inset,x2:x+thickness/2,y2:y+length-inset};
  vault.cx=(vault.x1+vault.x2)/2; vault.cy=(vault.y1+vault.y2)/2;
  vault.length=Math.hypot(vault.x2-vault.x1,vault.y2-vault.y1);
  return { kind:'lineVault', bbox:structureBBox([seg]), segments:[seg], vault };
}

function generateWorld() {
  const exitGates = [
    { x:WORLD_WIDTH/2-125, y:10, w:250, h:40, leverX:WORLD_WIDTH/2, leverY:60, progress:0, status:'inactive' },
    { x:WORLD_WIDTH/2-125, y:WORLD_HEIGHT-50, w:250, h:40, leverX:WORLD_WIDTH/2, leverY:WORLD_HEIGHT-70, progress:0, status:'inactive' }
  ];
  const reservedRects = [
    {x:WORLD_WIDTH/2-CENTER_CORRIDOR_HALF,y:0,w:CENTER_CORRIDOR_HALF*2,h:WORLD_HEIGHT},
    {x:0,y:WORLD_HEIGHT/2-CENTER_CORRIDOR_HALF,w:WORLD_WIDTH,h:CENTER_CORRIDOR_HALF*2},
    {x:exitGates[0].x-180,y:0,w:exitGates[0].w+360,h:260},
    {x:exitGates[1].x-180,y:WORLD_HEIGHT-260,w:exitGates[1].w+360,h:260},
    {x:PLAYER_START_1.x-220,y:PLAYER_START_1.y-220,w:440,h:440},
    {x:KILLER_START.x-220,y:KILLER_START.y-220,w:440,h:440}
  ];

  function isPointFair(x, y, extra=0) {
    for(const r of reservedRects) if(pointInRect(x,y,r,extra)) return false;
    for(const o of obstacles) if(circleRectOverlap(x,y,extra,o,30)) return false;
    return true;
  }
  function canPlaceStructure(c) {
    if(c.bbox.x<70||c.bbox.y<70||c.bbox.x+c.bbox.w>WORLD_WIDTH-70||c.bbox.y+c.bbox.h>WORLD_HEIGHT-70) return false;
    for(const r of reservedRects) if(rectsOverlap(c.bbox,r,0)) return false;
    for(const s of structures) if(rectsOverlap(c.bbox,s.bbox,78)) return false;
    return true;
  }
  function canPlaceGenerator(c) {
    if(!isPointFair(c.x,c.y,GENERATOR_WORKSPACE)) return false;
    for(const g of generators) if(Math.hypot(c.x-g.x,c.y-g.y)<430) return false;
    for(const l of lockers) if(Math.hypot(c.x-(l.x+l.w/2),c.y-(l.y+l.h/2))<190) return false;
    for(const v of vaults) if(Math.hypot(c.x-v.cx,c.y-v.cy)<170) return false;
    return true;
  }
  function canPlaceLocker(c) {
    if(!isPointFair(c.x+c.w/2,c.y+c.h/2,72)) return false;
    for(const g of generators) if(circleRectOverlap(g.x,g.y,GENERATOR_WORKSPACE,c,40)) return false;
    for(const l of lockers) if(Math.hypot((l.x+l.w/2)-(c.x+c.w/2),(l.y+l.h/2)-(c.y+c.h/2))<LOCKER_MIN_DISTANCE) return false;
    for(const v of vaults) if(circleRectOverlap(v.cx,v.cy,90,c,20)) return false;
    return true;
  }

  const structures=[], obstacles=[], vaults=[], generators=[], lockers=[];

  let tries=0;
  do {
    tries++;
    structures.length=0; vaults.length=0; obstacles.length=0; generators.length=0; lockers.length=0;
    let attempt=0;
    while(structures.length<24 && attempt<5000) {
      attempt++;
      let c;
      if(Math.random()<0.65) {
        const size=Math.random()*170+180, arm=Math.random()*120+140;
        c=buildLStructure(Math.random()*(WORLD_WIDTH-size-160)+80,Math.random()*(WORLD_HEIGHT-size-160)+80,size,arm,Math.floor(Math.random()*4));
      } else {
        const w=Math.random()*170+220, h=Math.random()*170+220;
        c=buildDStructure(Math.random()*(WORLD_WIDTH-w-160)+80,Math.random()*(WORLD_HEIGHT-h-160)+80,w,h,Math.floor(Math.random()*4));
      }
      if(!canPlaceStructure(c)) continue;
      structures.push(c); for(const seg of c.segments) obstacles.push(seg); if(c.vault) vaults.push(c.vault);
    }
    attempt=0;
    while(generators.length<7 && attempt<5000) {
      attempt++;
      const c={x:Math.random()*(WORLD_WIDTH-500)+250,y:Math.random()*(WORLD_HEIGHT-500)+250,progress:0,fixed:false};
      if(canPlaceGenerator(c)) generators.push(c);
    }
    // anchor lockers near generators
    const angles=[0,Math.PI/2,Math.PI,Math.PI*1.5,Math.PI/4,Math.PI*.75,Math.PI*1.25,Math.PI*1.75];
    for(const g of generators) {
      let placed=false;
      for(const radius of [120,132,146,160]) {
        for(const angle of angles) {
          const cx=g.x+Math.cos(angle)*radius, cy=g.y+Math.sin(angle)*radius;
          const cand={x:cx-23,y:cy-34,w:46,h:68};
          if(!isPointFair(cand.x+cand.w/2,cand.y+cand.h/2,44)) continue;
          let ok=true;
          for(const g2 of generators) { if(g2===g) continue; if(circleRectOverlap(g2.x,g2.y,GENERATOR_WORKSPACE,cand,24)){ok=false;break;} }
          if(!ok) continue;
          for(const l of lockers) { if(Math.hypot((l.x+l.w/2)-(cand.x+cand.w/2),(l.y+l.h/2)-(cand.y+cand.h/2))<LOCKER_MIN_DISTANCE){ok=false;break;} }
          if(!ok) continue;
          for(const v of vaults) { if(circleRectOverlap(v.cx,v.cy,90,cand,20)){ok=false;break;} }
          if(ok) { lockers.push(cand); placed=true; break; }
        }
        if(placed) break;
      }
    }
    const zones=[{x:120,y:120,w:1180,h:1180},{x:1700,y:120,w:1180,h:1180},{x:120,y:1700,w:1180,h:1180},{x:1700,y:1700,w:1180,h:1180},{x:1260,y:160,w:480,h:780},{x:1260,y:2060,w:480,h:780}];
    attempt=0;
    while(lockers.length<18 && attempt<5000) {
      attempt++;
      const zone=zones[attempt%zones.length];
      const c={x:Math.random()*(zone.w-90)+zone.x,y:Math.random()*(zone.h-110)+zone.y,w:46,h:68};
      if(canPlaceLocker(c)) lockers.push(c);
    }
    // extra vault structures
    let added=0; attempt=0;
    while(added<2 && attempt<600) {
      attempt++;
      const horizontal=Math.random()<0.5;
      const c=buildLineVaultStructure(Math.random()*(WORLD_WIDTH-520)+80,Math.random()*(WORLD_HEIGHT-520)+80,horizontal);
      if(!canPlaceStructure(c)) continue;
      structures.push(c); for(const seg of c.segments) obstacles.push(seg); vaults.push(c.vault); added++;
    }
  } while((generators.length<7||lockers.length<15||structures.length<20) && tries<20);

  return { structures, obstacles, vaults, generators, lockers, exitGates };
}

// ── Room / lobby management ────────────────────────────────────────────────
const rooms = new Map(); // roomId → room

function createRoom(roomId) {
  const world = generateWorld();
  return {
    id: roomId,
    phase: 'lobby',      // lobby | character_select | playing | ended
    clients: new Map(),  // ws → { id, role, name, ready }
    world,
    game: null,
    selectTimer: null,
    charSelectDeadline: null,
  };
}

function broadcast(room, msg) {
  const data = JSON.stringify(msg);
  for(const [ws] of room.clients) {
    if(ws.readyState === WebSocket.OPEN) ws.send(data);
  }
}
function send(ws, msg) {
  if(ws.readyState === WebSocket.OPEN) ws.send(JSON.stringify(msg));
}

// ── Game state ─────────────────────────────────────────────────────────────
function initGame(room) {
  const { world } = room;
  const survivorIds = [...room.clients.values()].filter(c=>c.role==='survivor').map(c=>c.id);
  const killerId    = [...room.clients.values()].find(c=>c.role==='killer').id;

  const survivors = {};
  survivorIds.forEach((id, i) => {
    const start = i===0 ? PLAYER_START_1 : PLAYER_START_2;
    survivors[id] = {
      id, x:start.x, y:start.y,
      radius:18, walkSpeed:170, runSpeed:295,
      hp:2,                 // 2-hit system
      caged:false,
      cageTimer:0,
      cageId:null,
      invincible:0,         // seconds remaining of invincibility
      hitBoost:0,           // speed boost after first hit
      dead:false,
      isHiding:false,
      currentLocker:null,
      cabCooldown:0,
      vaultAction:null,
      angle:0,
      walkCycle:0,
      scratchTimer:0,
      repairNoiseTimer:0,
      interacting:false,
      actionProgress:0,
    };
  });

  const cages = [];   // { id, x, y, survivorId, timer, camping }

  const killerEntity = {
    id: killerId,
    x: KILLER_START.x, y: KILLER_START.y,
    radius:24, speed:340,
    angle:0,
    state:'patrol',
    targetX:KILLER_START.x, targetY:KILLER_START.y,
    targetGate:0,
    lastSeen:null,
    suspiciousLocker:null,
    inspectTimer:0,
    searchTimer:0,
    vaultAction:null,
    vaultCooldown:0,
    stuckTime:0,
  };

  return {
    survivors,
    killer: killerEntity,
    cages,
    gensFixed: 0,
    endgame: false,
    over: false,
    winner: null,      // 'survivors' | 'killer'
    lastTick: Date.now(),
    inputs: {},
    scratchMarks: [],
  };
}

// ── Physics helpers (server-side) ──────────────────────────────────────────
function checkCollision(px, py, radius, obstacles) {
  for(const obs of obstacles) {
    const nx=clamp(px,obs.x,obs.x+obs.w);
    const ny=clamp(py,obs.y,obs.y+obs.h);
    if(((px-nx)**2+(py-ny)**2)<=radius**2) return true;
  }
  return false;
}
function hasLineOfSight(x1,y1,x2,y2,obstacles) {
  const dist=Math.hypot(x2-x1,y2-y1);
  const steps=Math.max(2,Math.ceil(dist/18));
  for(let i=1;i<steps;i++){
    const t=i/steps, sx=x1+(x2-x1)*t, sy=y1+(y2-y1)*t;
    for(const obs of obstacles) if(pointInRect(sx,sy,obs,3)) return false;
  }
  return true;
}
function angleLerp(current,target,amount){
  let diff=target-current;
  while(diff>Math.PI)diff-=Math.PI*2; while(diff<-Math.PI)diff+=Math.PI*2;
  return current+diff*amount;
}
function distancePointToSegment(px,py,x1,y1,x2,y2){
  const dx=x2-x1,dy=y2-y1,lenSq=dx*dx+dy*dy||1;
  let t=((px-x1)*dx+(py-y1)*dy)/lenSq; t=clamp(t,0,1);
  return Math.hypot(px-x1-dx*t,py-y1-dy*t);
}
function findNearbyVault(px,py,range,vaults){
  let best=null,bestD=range;
  for(const v of vaults){
    const d=distancePointToSegment(px,py,v.x1,v.y1,v.x2,v.y2);
    if(d<bestD){bestD=d;best=v;}
  }
  return best;
}
function getVaultTarget(vault,entity,extra){
  if(vault.orientation==='horizontal'){
    const dir=entity.y<vault.cy?1:-1;
    return{x:clamp(entity.x,Math.min(vault.x1,vault.x2)+10,Math.max(vault.x1,vault.x2)-10),y:vault.cy+dir*extra};
  }
  const dir=entity.x<vault.cx?1:-1;
  return{x:vault.cx+dir*extra,y:clamp(entity.y,Math.min(vault.y1,vault.y2)+10,Math.max(vault.y1,vault.y2)-10)};
}
function moveEntity(entity,speed,dt,obstacles){
  const dist=speed*dt;
  const tryMove=(angle,scale=1)=>{
    const nx=clamp(entity.x+Math.cos(angle)*dist*scale,entity.radius,WORLD_WIDTH-entity.radius);
    const ny=clamp(entity.y+Math.sin(angle)*dist*scale,entity.radius,WORLD_HEIGHT-entity.radius);
    if(!checkCollision(nx,ny,entity.radius,obstacles)){entity.x=nx;entity.y=ny;return true;}
    return false;
  };
  if(tryMove(entity.angle)){entity.stuckTime=0;return true;}
  for(const off of[0.35,-0.35,0.7,-0.7,1.1,-1.1,Math.PI/2,-Math.PI/2]){
    if(tryMove(entity.angle+off,0.92)){entity.angle=angleLerp(entity.angle,entity.angle+off,0.35);entity.stuckTime=0;return true;}
  }
  entity.stuckTime=(entity.stuckTime||0)+dt;
  if(entity.stuckTime>0.25){entity.angle+=(Math.random()<0.5?1:-1)*(0.8+Math.random()*0.8);entity.stuckTime=0;}
  return false;
}
function setPatrolTarget(killer,generators){
  const active=generators.filter(g=>!g.fixed);
  const pool=active.length?active:generators;
  const g=pool[Math.floor(Math.random()*pool.length)]||{x:WORLD_WIDTH/2,y:WORLD_HEIGHT/2};
  killer.targetX=g.x+(Math.random()-0.5)*170;
  killer.targetY=g.y+(Math.random()-0.5)*170;
}
function canUseVaultToward(vault,entity,tx,ty){
  if(vault.orientation==='horizontal') return(entity.y-vault.cy)*(ty-vault.cy)<0&&Math.abs(entity.x-vault.cx)<vault.length*0.7;
  return(entity.x-vault.cx)*(tx-vault.cx)<0&&Math.abs(entity.y-vault.cy)<vault.length*0.7;
}

// ── Cage helpers ───────────────────────────────────────────────────────────
let cageIdCounter = 0;
function spawnCage(game, survivorId, world) {
  // find a random fair position
  let cx, cy, tries=0;
  do {
    cx = Math.random()*(WORLD_WIDTH-400)+200;
    cy = Math.random()*(WORLD_HEIGHT-400)+200;
    tries++;
  } while(tries<100 && checkCollision(cx,cy,80,world.obstacles));
  const cage = { id: `cage_${cageIdCounter++}`, x:cx, y:cy, survivorId, timer:60, camping:false };
  game.cages.push(cage);
  const s = game.survivors[survivorId];
  s.caged = true;
  s.cageTimer = 60;
  s.cageId = cage.id;
  s.x = cx; s.y = cy;
  return cage;
}

// ── Game tick ──────────────────────────────────────────────────────────────
const REPAIR_RATE = 100/30; // 30 seconds per generator
const CAGE_CAMPING_RADIUS = 400;
const CAGE_RESCUE_RADIUS = 100;

function tickGame(room, dt) {
  const game = room.game;
  const world = room.world;
  const { killer, survivors, cages } = game;
  const obs = world.obstacles;
  const vaults = world.vaults;

  if(game.over) return;

  // ── Killer AI update ──
  const killerInput = game.inputs[killer.id] || {};

  // If killer is human-controlled
  if(killerInput.human) {
    // Human killer movement
    if(killer.vaultAction) {
      const v=killer.vaultAction;
      v.elapsed+=dt;
      const t=clamp(v.elapsed/v.duration,0,1);
      killer.x=lerp2(v.startX,v.targetX,t); killer.y=lerp2(v.startY,v.targetY,t);
      if(t>=1) killer.vaultAction=null;
    } else {
      if(killerInput.angle!==undefined) killer.angle=killerInput.angle;
      if(killerInput.moving) moveEntity(killer,killer.speed*0.9,dt,obs);
      if(killerInput.vault && !killer.vaultAction && (!killer.vaultCooldown||killer.vaultCooldown<=0)) {
        const vault=findNearbyVault(killer.x,killer.y,42,vaults);
        if(vault){ const target=getVaultTarget(vault,killer,82); killer.vaultAction={vault,startX:killer.x,startY:killer.y,targetX:target.x,targetY:target.y,duration:2.0,elapsed:0}; killer.vaultCooldown=0.6; }
      }
    }
    if(killer.vaultCooldown>0) killer.vaultCooldown=Math.max(0,killer.vaultCooldown-dt);
  } else {
    // AI killer (fallback - shouldn't normally happen since we require human killer)
    updateAIKiller(killer, survivors, game, world, dt);
  }

  // ── Survivor updates ──
  for(const [sid, s] of Object.entries(survivors)) {
    if(s.dead) continue;

    // invincibility countdown
    if(s.invincible>0) s.invincible=Math.max(0,s.invincible-dt);
    if(s.hitBoost>0) s.hitBoost=Math.max(0,s.hitBoost-dt);

    // cab cooldown
    if(s.cabCooldown>0) s.cabCooldown=Math.max(0,s.cabCooldown-dt);

    if(s.caged) {
      // handled in cage section below
      continue;
    }

    const inp = game.inputs[sid] || {};

    // Vault action
    if(s.vaultAction) {
      const v=s.vaultAction;
      v.elapsed+=dt;
      const t=clamp(v.elapsed/v.duration,0,1);
      s.x=lerp2(v.startX,v.targetX,t); s.y=lerp2(v.startY,v.targetY,t);
      s.interacting=true; s.actionProgress=t*100;
      if(t>=1) s.vaultAction=null;
      continue;
    }

    s.interacting=false;

    // Cabinet toggle
    if(inp.fJust) {
      if(s.isHiding) {
        const locker=s.currentLocker;
        s.isHiding=false; s.currentLocker=null; s.cabCooldown=10;
        if(locker){ s.x=clamp(locker.x+locker.w+30,s.radius,WORLD_WIDTH-s.radius); s.y=clamp(locker.y+locker.h/2,s.radius,WORLD_HEIGHT-s.radius); }
      } else if(s.cabCooldown<=0) {
        const locker=findNearbyLocker2(s.x,s.y,30,world.lockers);
        if(locker){ s.isHiding=true; s.currentLocker=locker; s.x=locker.x+locker.w/2; s.y=locker.y+locker.h/2; }
      }
    }

    if(s.isHiding) continue;

    // Movement
    let dx=0,dy=0;
    if(inp.w) dy-=1; if(inp.s) dy+=1; if(inp.a) dx-=1; if(inp.d) dx+=1;
    if(dx!==0&&dy!==0){dx*=0.70710678;dy*=0.70710678;}
    let spd = inp.shift ? s.runSpeed : s.walkSpeed;
    if(s.hitBoost>0) spd=s.runSpeed*1.5; // speed boost after first hit
    const nx=s.x+dx*spd*dt, ny=s.y+dy*spd*dt;
    if(!checkCollision(nx,s.y,s.radius,obs)) s.x=clamp(nx,s.radius,WORLD_WIDTH-s.radius);
    if(!checkCollision(s.x,ny,s.radius,obs)) s.y=clamp(ny,s.radius,WORLD_HEIGHT-s.radius);
    if(dx!==0||dy!==0){
      s.walkCycle+=(inp.shift?7.5:4)*dt;
      s.angle=Math.atan2(dy,dx);
      s.isRunning=inp.shift;
      if(inp.shift){
        s.scratchTimer=(s.scratchTimer||0)+dt;
        while(s.scratchTimer>=0.06){
          s.scratchTimer-=0.06;
          game.scratchMarks.push({x:s.x+(Math.random()-0.5)*22,y:s.y+(Math.random()-0.5)*22,angle:Math.atan2(dy,dx)+(Math.random()-0.5),t:Date.now()});
        }
      } else { s.scratchTimer=0; }
    } else { s.isRunning=false; }

    // E - vault or generator repair or rescue or exit
    if(inp.e) {
      // Vault
      const vault=findNearbyVault(s.x,s.y,34,vaults);
      if(vault&&!s.vaultAction){
        const target=getVaultTarget(vault,s,78);
        s.vaultAction={vault,startX:s.x,startY:s.y,targetX:target.x,targetY:target.y,duration:0.5,elapsed:0};
        s.interacting=true;
      } else {
        // Generator repair
        if(!game.endgame) {
          for(const g of world.generators) {
            if(!g.fixed && Math.hypot(s.x-g.x,s.y-g.y)<74) {
              s.interacting=true; s.actionProgress=g.progress;
              g.progress=Math.min(100,g.progress+REPAIR_RATE*dt);
              s.repairNoiseTimer=(s.repairNoiseTimer||0)+dt;
              if(s.repairNoiseTimer>=0.95){
                s.repairNoiseTimer=0;
                broadcast(room,{type:'repairNoise',x:g.x,y:g.y});
              }
              // skill check chance
              if(Math.random()<0.19*dt) broadcast(room,{type:'skillCheck',survivorId:sid});
              if(g.progress>=100){
                g.fixed=true; game.gensFixed++;
                broadcast(room,{type:'genFixed',genIndex:world.generators.indexOf(g),gensFixed:game.gensFixed});
                if(game.gensFixed>=5){
                  game.endgame=true;
                  world.exitGates.forEach(eg=>eg.status='powered');
                  broadcast(room,{type:'endgame'});
                }
              }
              break;
            }
          }
        }
        // Exit gate
        if(game.endgame) {
          for(const eg of world.exitGates) {
            if((eg.status==='powered'||eg.status==='opening')&&Math.hypot(s.x-eg.leverX,s.y-eg.leverY)<62){
              s.interacting=true; eg.status='opening';
              eg.progress=Math.min(100,eg.progress+18*dt);
              s.actionProgress=eg.progress;
              if(eg.progress>=100){ eg.status='open'; broadcast(room,{type:'gateOpen',gateIndex:world.exitGates.indexOf(eg)}); }
              break;
            }
          }
          // Walk through open gate
          for(const eg of world.exitGates) {
            if(eg.status==='open'&&s.x>eg.x&&s.x<eg.x+eg.w&&s.y>eg.y-24&&s.y<eg.y+eg.h+24) {
              s.dead=true; // escaped (count as survived)
              broadcast(room,{type:'survivorEscaped',survivorId:sid});
            }
          }
        }
        // Cage rescue
        for(const cage of cages) {
          if(!cage.survivorId) continue;
          const cs=survivors[cage.survivorId];
          if(cs&&cs.caged&&cage.survivorId!==sid&&Math.hypot(s.x-cage.x,s.y-cage.y)<CAGE_RESCUE_RADIUS) {
            // rescuing
            s.interacting=true; s.actionProgress=(1-(cage.timer/60))*100;
            cage.rescueProgress=(cage.rescueProgress||0)+dt;
            if(cage.rescueProgress>=3) { // 3 seconds to rescue
              rescueSurvivor(cs,cage,game);
              broadcast(room,{type:'rescued',survivorId:cage.survivorId,rescuerId:sid});
            }
            break;
          }
        }
      }
    } else {
      s.repairNoiseTimer=0;
      if(s.interacting) s.interacting=false;
    }

    // Killer catch
    if(s.invincible<=0 && !s.caged) {
      const dist=Math.hypot(s.x-killer.x,s.y-killer.y);
      if(dist<s.radius+killer.radius) {
        hitSurvivor(s, sid, game, world, room);
      }
    }
  }

  // ── Cage timers ──
  for(const cage of cages) {
    if(!cage.survivorId) continue;
    const s=survivors[cage.survivorId];
    if(!s||!s.caged) { cage.survivorId=null; continue; }

    // Check camping: killer within CAGE_CAMPING_RADIUS
    const killerDist=Math.hypot(killer.x-cage.x,killer.y-cage.y);
    const wasCamping=cage.camping;
    cage.camping=killerDist<CAGE_CAMPING_RADIUS;
    if(cage.camping!==wasCamping) broadcast(room,{type:'campingChange',cageId:cage.id,camping:cage.camping});

    if(!cage.camping) {
      cage.timer=Math.max(0,cage.timer-dt);
      s.cageTimer=cage.timer;
      if(cage.timer<=0) {
        // Survivor dies
        s.dead=true; s.caged=false;
        broadcast(room,{type:'survivorDied',survivorId:cage.survivorId});
        cage.survivorId=null;
        checkVictory(room, game, world);
      }
    }
    // Reset rescue progress if killer is camping
    if(cage.camping) cage.rescueProgress=0;
  }

  // ── Victory check ──
  checkVictory(room, game, world);

  // ── Broadcast state ──
  broadcastState(room);
}

function lerp2(a,b,t){return a+(b-a)*t;}

function findNearbyLocker2(px,py,range,lockers){
  for(const l of lockers) if(px>l.x-range&&px<l.x+l.w+range&&py>l.y-range&&py<l.y+l.h+range) return l;
  return null;
}

function hitSurvivor(s, sid, game, world, room) {
  if(s.invincible>0) return;
  if(s.hp===2) {
    // First hit: speed boost, 3s invincible
    s.hp=1;
    s.invincible=3;
    s.hitBoost=3;
    broadcast(room,{type:'survivorHit',survivorId:sid,hp:1});
  } else {
    // Second hit: cage
    s.hp=0;
    const cage=spawnCage(game,sid,world);
    broadcast(room,{type:'survivorCaged',survivorId:sid,cage:{id:cage.id,x:cage.x,y:cage.y}});
    // Check if all survivors caged/dead
    checkVictory(room,game,world);
  }
}

function rescueSurvivor(s, cage, game) {
  s.caged=false; s.cageId=null; s.invincible=5; s.hp=2;
  s.x=cage.x+100; s.y=cage.y;
  cage.survivorId=null; cage.rescueProgress=0;
}

function checkVictory(room, game, world) {
  if(game.over) return;
  const aliveOrFree=[...Object.values(game.survivors)].filter(s=>!s.dead||s.caged);
  const allDead=Object.values(game.survivors).every(s=>s.dead&&!s.caged);
  const allCaged=Object.values(game.survivors).filter(s=>!s.dead).every(s=>s.caged);

  if(allDead||(allCaged&&Object.values(game.survivors).every(s=>s.dead||s.caged))) {
    game.over=true; game.winner='killer';
    broadcast(room,{type:'gameOver',winner:'killer'});
    room.phase='ended';
    return;
  }
  // survivors win if all escaped (dead flag used for escaped)
  // We track escaped separately
  const escaped=Object.values(game.survivors).filter(s=>s.escaped).length;
  if(escaped>0 && Object.values(game.survivors).every(s=>s.escaped||s.dead)) {
    game.over=true; game.winner='survivors';
    broadcast(room,{type:'gameOver',winner:'survivors'});
    room.phase='ended';
  }
}

function updateAIKiller(killer, survivors, game, world, dt) {
  // Simple AI patrol toward generators (fallback)
  const obs=world.obstacles;
  const vaults=world.vaults;
  if(killer.vaultCooldown>0) killer.vaultCooldown=Math.max(0,killer.vaultCooldown-dt);

  let closestSurvivor=null, closestDist=Infinity;
  for(const s of Object.values(survivors)) {
    if(s.dead||s.caged||s.isHiding) continue;
    const d=Math.hypot(s.x-killer.x,s.y-killer.y);
    if(d<closestDist){closestDist=d;closestSurvivor=s;}
  }
  if(closestSurvivor&&closestDist<500&&hasLineOfSight(killer.x,killer.y,closestSurvivor.x,closestSurvivor.y,obs)){
    killer.state='chase'; killer.lastSeen={x:closestSurvivor.x,y:closestSurvivor.y};
  }
  if(killer.state==='chase'&&closestSurvivor){
    const tx=closestSurvivor.x, ty=closestSurvivor.y;
    const ta=Math.atan2(ty-killer.y,tx-killer.x);
    killer.angle=angleLerp(killer.angle,ta,clamp(8*dt,0,1));
    moveEntity(killer,killer.speed*0.9,dt,obs);
  } else {
    killer.state='patrol';
    if(Math.hypot(killer.targetX-killer.x,killer.targetY-killer.y)<60) setPatrolTarget(killer,world.generators);
    const ta=Math.atan2(killer.targetY-killer.y,killer.targetX-killer.x);
    killer.angle=angleLerp(killer.angle,ta,clamp(4*dt,0,1));
    moveEntity(killer,killer.speed*0.92,dt,obs);
  }
}

function broadcastState(room) {
  const game=room.game;
  const survivorStates={};
  for(const [id,s] of Object.entries(game.survivors)) {
    survivorStates[id]={id,x:s.x,y:s.y,angle:s.angle,walkCycle:s.walkCycle||0,hp:s.hp,caged:s.caged,dead:s.dead,escaped:s.escaped||false,invincible:s.invincible>0,hitBoost:s.hitBoost>0,isHiding:s.isHiding,interacting:s.interacting,actionProgress:s.actionProgress,cageTimer:s.cageTimer||0,cabCooldown:s.cabCooldown||0,isRunning:s.isRunning||false};
  }
  const cageStates=game.cages.map(c=>({id:c.id,x:c.x,y:c.y,survivorId:c.survivorId,timer:c.timer,camping:c.camping}));
  const now_ms=Date.now();
  game.scratchMarks=game.scratchMarks.filter(m=>now_ms-m.t<3000);
  const scratchStates=game.scratchMarks.map(m=>({x:m.x,y:m.y,angle:m.angle,life:1-(now_ms-m.t)/3000}));
  broadcast(room,{
    type:'state',
    killer:{x:game.killer.x,y:game.killer.y,angle:game.killer.angle,state:game.killer.state,vaulting:!!game.killer.vaultAction},
    survivors:survivorStates,
    cages:cageStates,
    gensFixed:game.gensFixed,
    generators:room.world.generators.map(g=>({x:g.x,y:g.y,progress:g.progress,fixed:g.fixed})),
    exitGates:room.world.exitGates,
    endgame:game.endgame,
    scratchMarks:scratchStates,
  });
}

// ── Tick loop ──────────────────────────────────────────────────────────────
setInterval(()=>{
  for(const room of rooms.values()) {
    if(room.phase!=='playing'||!room.game) continue;
    const now=Date.now();
    const dt=Math.min(0.05,(now-room.game.lastTick)/1000);
    room.game.lastTick=now;
    tickGame(room,dt);
  }
},1000/30); // 30 Hz

// ── Character select timer ─────────────────────────────────────────────────
function startCharacterSelect(room) {
  room.phase='character_select';
  room.charSelectDeadline=Date.now()+30000;
  broadcast(room,{type:'characterSelect',deadline:room.charSelectDeadline,clients:[...room.clients.values()].map(c=>({id:c.id,name:c.name}))});
  room.selectTimer=setTimeout(()=>{
    // Auto-assign remaining roles
    autoAssignRoles(room);
    startGame(room);
  },30000);
}

function autoAssignRoles(room) {
  const clients=[...room.clients.values()];
  const hasKiller=clients.some(c=>c.role==='killer');
  if(!hasKiller){
    const unassigned=clients.find(c=>!c.role);
    if(unassigned) unassigned.role='killer';
  }
  for(const c of clients) if(!c.role) c.role='survivor';
}

function startGame(room) {
  if(room.selectTimer){ clearTimeout(room.selectTimer); room.selectTimer=null; }
  autoAssignRoles(room);
  room.phase='playing';
  room.game=initGame(room);
  // Send world data
  broadcast(room,{type:'startGame',world:{
    structures:room.world.structures,
    obstacles:room.world.obstacles,
    vaults:room.world.vaults,
    generators:room.world.generators,
    lockers:room.world.lockers,
    exitGates:room.world.exitGates,
  },roles:Object.fromEntries([...room.clients.values()].map(c=>[c.id,c.role]))});
}

// ── WebSocket server ───────────────────────────────────────────────────────
const wss = new WebSocketServer({ server: httpServer });

wss.on('connection', (ws) => {
  const clientId = `player_${Date.now()}_${Math.random().toString(36).slice(2,7)}`;
  const roomId = 'main'; // single room for now

  let room = rooms.get(roomId);
  if(!room){ room=createRoom(roomId); rooms.set(roomId,room); }

  if(room.clients.size>=3&&room.phase!=='lobby'){
    send(ws,{type:'error',msg:'방이 꽉 찼습니다.'}); ws.close(); return;
  }

  const clientInfo = { id:clientId, ws, role:null, name:`플레이어${room.clients.size+1}`, ready:false };
  room.clients.set(ws, clientInfo);

  send(ws,{type:'joined',id:clientId,playerCount:room.clients.size,phase:room.phase});
  broadcast(room,{type:'playerCount',count:room.clients.size});

  ws.on('message', (raw) => {
    let msg;
    try { msg=JSON.parse(raw); } catch { return; }
    const client=room.clients.get(ws);
    if(!client) return;

    switch(msg.type) {
      case 'setName':
        client.name=msg.name.slice(0,12)||client.name;
        broadcast(room,{type:'playerList',players:[...room.clients.values()].map(c=>({id:c.id,name:c.name,role:c.role}))});
        break;

      case 'ready':
        client.ready=true;
        broadcast(room,{type:'playerList',players:[...room.clients.values()].map(c=>({id:c.id,name:c.name,role:c.role,ready:c.ready}))});
        if(room.clients.size>=3 && [...room.clients.values()].every(c=>c.ready) && room.phase==='lobby') {
          startCharacterSelect(room);
        }
        break;

      case 'selectRole': {
        if(room.phase!=='character_select') break;
        const wantedRole=msg.role;
        const clients=[...room.clients.values()];
        const killerTaken=clients.some(c=>c!==client&&c.role==='killer');
        const survivorCount=clients.filter(c=>c!==client&&c.role==='survivor').length;
        if(wantedRole==='killer'&&!killerTaken){ client.role='killer'; }
        else if(wantedRole==='survivor'&&survivorCount<2){ client.role='survivor'; }
        else if(wantedRole==='killer'&&killerTaken){ client.role='survivor'; } // fallback
        broadcast(room,{type:'roleUpdate',players:clients.map(c=>({id:c.id,name:c.name,role:c.role}))});
        // Start if all 3 have roles and exactly 1 killer + 2 survivors
        const killerCount=clients.filter(c=>c.role==='killer').length;
        const survCount=clients.filter(c=>c.role==='survivor').length;
        if(killerCount===1&&survCount===2) {
          startGame(room);
        }
        break;
      }

      case 'input':
        if(room.phase==='playing'&&room.game) {
          const prev=room.game.inputs[client.id]||{};
          const inp=msg.input;
          // fJust = pressed this frame but not last frame
          inp.fJust = inp.f && !prev.f;
          inp.human = true;
          room.game.inputs[client.id]=inp;
          // Killer: check locker with fJust
          if(client.role==='killer' && inp.fJust && room.game) {
            const k=room.game.killer;
            for(const l of room.world.lockers){
              if(k.x>l.x-50&&k.x<l.x+l.w+50&&k.y>l.y-50&&k.y<l.y+l.h+50){
                // Check if survivor hiding in this locker
                for(const [sid,surv] of Object.entries(room.game.survivors)){
                  if(surv.isHiding && surv.currentLocker &&
                     Math.abs(surv.currentLocker.x-l.x)<1 && Math.abs(surv.currentLocker.y-l.y)<1){
                    // Kill them
                    surv.isHiding=false; surv.currentLocker=null;
                    const cage=spawnCage(room.game,sid,room.world);
                    broadcast(room,{type:'survivorCaged',survivorId:sid,cage:{id:cage.id,x:cage.x,y:cage.y}});
                    checkVictory(room,room.game,room.world);
                    break;
                  }
                }
                broadcast(room,{type:'lockerCheck',x:l.x+l.w/2,y:l.y+l.h/2});
                break;
              }
            }
          }
        }
        break;

      case 'skillCheckResult':
        if(room.phase==='playing'&&room.game) {
          if(!msg.success){
            // fail: reduce gen progress
            for(const g of room.world.generators) {
              if(!g.fixed&&Math.hypot(game.survivors[client.id]?.x-g.x,game.survivors[client.id]?.y-g.y)<74){
                g.progress=Math.max(0,g.progress-10); break;
              }
            }
          }
        }
        break;
    }
  });

  ws.on('close', () => {
    room.clients.delete(ws);
    broadcast(room,{type:'playerCount',count:room.clients.size});
    if(room.clients.size===0){ rooms.delete(roomId); }
    else if(room.phase==='playing'&&room.game) {
      broadcast(room,{type:'playerDisconnected',id:clientId});
    }
  });
});

httpServer.listen(PORT, ()=>console.log(`🎮 서버 실행 중: http://localhost:${PORT}`));
