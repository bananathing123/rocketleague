'use strict';
// ====================================================================================================
// Server-side match simulation.  The Render server is the HOST of every online match: it runs the exact same car / ball /
// bot / scoring code the game used to run inside the host's browser, then streams the world to every player (see server.js).
// One makeSim() = one match; all state lives inside the closure so many matches can run side by side.
// (Physics + bot AI below are copied from index.html - if you change one, change the other.)
// ====================================================================================================
const { Vector3, Quaternion } = require('./vec');
const T = { Vector3, Quaternion };
const V = (x, y, z) => new Vector3(x, y, z);

function makeSim() {
const GOAL_T = 4, SS_ON = 22, SS_OFF = 21;
const HX=41,HY=10.25,HZ=51,R=4.2,GW=8.95,GH=6.4,GD=8.8,GZ0=HZ-R;
const BOOST_DRAIN=20;   // boost used per second (was 33.3)
const RH=.22,MAXV=14.1,n=V(0,1,0),n2=V(0,1,0);
const BR=.9125,b=V(0,BR,0),bv=V(0,0,0),bq=new T.Quaternion(),w=V(0,0,0),nb=V(0,1,0),dodgeW=V(0,0,0),bw=V(0,0,0);
const HB_HH = .24, HB_CY = .17;
const cl=(v,m)=>Math.max(-m,Math.min(m,v));
function bdepth(px,py,pz,cx,cy,cz,hx,hy,hz,r){const qx=Math.abs(px-cx)-hx+r,qy=Math.abs(py-cy)-hy+r,qz=Math.abs(pz-cz)-hz+r;
 return -(Math.hypot(Math.max(qx,0),Math.max(qy,0),Math.max(qz,0))+Math.min(Math.max(qx,qy,qz),0)-r)}
const gcz=(GZ0+HZ+GD)/2,ghz=(HZ+GD-GZ0)/2;
const rr=(x,low)=>{if(!low)return R;const t=Math.max(0,Math.min(1,(Math.abs(x)-GW)/8));return R*(.03+.97*t*t*(3-2*t))};
function depth(p){const z=Math.abs(p.z);return Math.max(bdepth(p.x,p.y,p.z,0,HY,0,HX,HY,HZ,rr(p.x,p.y<HY)),gdepth(p.x,p.y,z))}
function gdepth(x,y,z){ // ONE goal volume that starts inside the arena (so it overlaps the open floor, no thin slab at the mouth) - sharp at the mouth, curved corners a couple of metres inside
 const cz=(GZ0+HZ+GD)/2,hz=(HZ+GD-GZ0)/2,sh=bdepth(x,y,z,0,GH/2,cz,GW,GH/2,hz,0),rd=bdepth(x,y,z,0,GH/2,cz,GW,GH/2,hz,1),t=Math.max(0,Math.min(1,(z-HZ)/2.2)),s=t*t*(3-2*t);return sh+(rd-sh)*s}
function normal(p,o=V(0,0,0)){const e=.02,q=p.clone();
 const g=(a)=>{q.copy(p);q[a]+=e;const u=depth(q);q[a]-=2*e;return u-depth(q)};
 return o.set(g('x'),g('y'),g('z')).normalize()}

// ---------- events (sounds / explosions / feed lines) that the server forwards to the players ----------
let evq = [];
const emitEv = (list, to) => { for (const e of list) evq.push({ e, to }); };
const sfxAt = (nm, pos, vol) => emitEv([['s', nm, +pos.x.toFixed(1), +pos.y.toFixed(1), +pos.z.toFixed(1), vol == null ? 1 : vol]]);
const explode = (pos, team, sc) => emitEv([['x', pos.x, pos.y, pos.z, team, sc || 1]]);
const killAdd = (a, v) => emitEv([['k', a.n, a.t, v.n, v.t]]);
const award = (st, pts, label) => { st.score += pts; if (st.nid > 0 && pts > 2 && !matchEnd) emitEv([['d', pts]], st.nid); };

// ---------- match state ----------
let phase = 0, simT = 0, goalT = 0, goalAt = 0, goalTeam = 0, cdT = 0, goT = 0, rt = 0, rIdx = 0, lastHitT = -1, lastBnc = 0, lastBump = 0, lastSec = 0;
let score = [0, 0], mTime = 120, lenSec = 120, ot = false, otT = 0, matchEnd = false, tUp = 0, seq = 0, ballVisible = true, mDiff = 1;
let koFirst = true, firstKo = true, goalInfo = null, lastTc = null, prevTc = null, pend = null, koIdx = [0, 1, 2, 3, 4];
const goalPos = V(0, 0, 0), hitT = [-1, -1], hist = [], bots = [], pads = [];   // bots = EVERY car (humans have pl:1, AI cars pl:0)
const KP = [[-20.48, -25.6], [20.48, -25.6], [-2.56, -38.4], [2.56, -38.4], [0, -46.08]];
const DIFF = [
 {n:'Rookie',sp:.62,re:.6,er:3.2,bu:.2,fl:0,ae:0,hz:1.5,mi:.45,sm:0},
 {n:'Pro',sp:.88,re:.22,er:1.2,bu:.7,fl:.7,ae:6,hz:2.5,mi:.12,sm:1},
 {n:'All-Star',sp:1,re:.08,er:.25,bu:1,fl:1,ae:10.5,hz:3.4,mi:0,sm:1}];
[[-30.7,-41],[30.7,-41],[-30.7,41],[30.7,41],[-35.8,0],[35.8,0]].forEach(a => pads.push({ x: a[0], z: a[1], big: 1, t: 0 }));
[[0,43],[12,41],[22,30],[8,28],[14,14],[0,16],[26,6]].forEach(([x, z]) => { for (const sx of x ? [-1, 1] : [1]) for (const sz of [-1, 1]) pads.push({ x: sx * x, z: sz * z, big: 0, t: 0 }); });

function mkS(x,z,yaw){return{p:V(x,.22,z),v:V(0,0,0),q:new T.Quaternion().setFromAxisAngle(V(0,1,0),yaw),w:V(0,0,0),dodgeW:V(0,0,0),boost:33,jumpT:0,hasJump:false,airT:0,dodgeT:0,ceilT:0,jcool:0,jprev:false,dodged:false,selfFlip:false,restT:0,isAir:false,isBoost:false,dFw:0,dRt:0,hc:0,t:0,dead:0,st:null}}
function mkSt(n,t,sub){return{n:n,t:t,sub:sub||'',score:0,goals:0,assists:0,saves:0,shots:0,demos:0,mvp:0,tT:-9}}
const AIDEF = () => ({rt:0,tx:0,ty:0,tz:0,kx:0,ky:0,kz:0,act:null,at:0,fs:0,cd:0,stk:0,mode:'atk',aer:false,ta:0,fl:false,bo:false,mis:0,fr:0});
function addCar(pl) {
  const C = mkS(0, 0, 0); C.t = pl.team;
  const st = mkSt(pl.name, pl.team, pl.bot ? 'BOT' : 'PLAYER'); st.nid = pl.id; C.st = st;
  const o = { id: pl.id, name: pl.name, t: pl.team, C, st, idx: 0, pl: pl.bot ? 0 : 1, jh: 0, I: { thr: 0, st: 0, roll: 0, sl: 0, bo: 0, jump: 0, jr: 0 }, ai: AIDEF() };
  bots.push(o); return o;
}

// ---------- bot AI (unchanged) ----------
const pn=V(0,1,0);let pred=[],predT=0;
function predictBall(N,DT){const pp=b.clone(),vv=bv.clone(),out=[];for(let i=1;i<=N;i++){vv.y-=6.5*DT;vv.multiplyScalar(1-.03*DT);pp.addScaledVector(vv,DT);const d=depth(pp);
  if(d<BR){normal(pp,pn);pp.addScaledVector(pn,BR-d);const vn=vv.dot(pn);if(vn<0)vv.addScaledVector(pn,-(1+(Math.abs(vn)<1.5?.15:.6))*vn)}out.push({t:i*DT,x:pp.x,y:pp.y,z:pp.z})}return out}
const etaB=C=>Math.hypot(b.x-C.p.x,b.z-C.p.z)/(C.boost>6?19:14)+(b.y>3?.4:0);
function nearPad(C){let best=null,bd=1e9;for(const a of pads){if(a.t>1.6)continue;const d=Math.hypot(a.x-C.p.x,a.z-C.p.z)-(a.big?10:0);if(d<bd){bd=d;best=a}}return best}
function botsAI(dt,live){if(!bots.length)return;const D=DIFF[mDiff];
 if(!live){for(const o of bots){if(o.pl)continue;const I=o.I;I.thr=I.st=I.roll=I.sl=I.bo=I.jump=0}return}
 predT-=dt;if(predT<=0||!pred.length){predT=.1;pred=predictBall(Math.round(D.hz/.1),.1)}
 const ko=Math.hypot(b.x,b.z)<1.3&&bv.lengthSq()<1;
 const cars=bots.slice();cars.forEach(c=>c.al=!(c.C.dead>0));
 for(const t of[0,1]){const gz=t?-HZ:HZ,og=-Math.sign(gz),mates=cars.filter(c=>c.t==t&&c.al),opps=cars.filter(c=>c.t!=t&&c.al);
  mates.forEach(c=>c.e=etaB(c.C));const oE=Math.min(...opps.map(c=>etaB(c.C))),ord=mates.slice().sort((a,c)=>a.e-c.e);
  const danger=pred.some(k=>Math.sign(k.z)==og&&Math.abs(k.z)>HZ-2.5&&Math.abs(k.x)<GW+1&&k.y<GH+1)||Math.abs(b.z-og*HZ)<22,nonAtk=ord.slice(1).filter(c=>!c.pl);
  for(const o of mates){if(o.pl)continue;const ai=o.ai,rk=ord.indexOf(o);
   let role=rk==0?'atk':(rk==1?'sup':'gk');
   if(mates.length==1&&D.sm&&o.e>oE+.7&&Math.abs(b.z-og*HZ)<52)role='sh';
   if(role!='atk'&&danger&&nonAtk[0]===o)role='atk';
   ai.rt-=dt;if(ai.rt<=0||ai.mode!=role){ai.rt=D.re*(.7+Math.random()*.6);replan(o,role,D,ko)}
   drive(o,D,ko,dt)}}}
function replan(o,role,D,ko){const C=o.C,ai=o.ai,t=o.t,gz=t?-HZ:HZ,og=-Math.sign(gz),er=()=>(Math.random()-.5)*2*D.er;
 ai.mode=role;ai.aer=false;ai.fl=Math.random()<D.fl;ai.bo=Math.random()<D.bu;if(Math.random()<D.mi)ai.mis=.5;
 if(D.sm&&((role!='atk'&&(C.boost<40||(ko&&C.boost<60)))||(role=='atk'&&C.boost<12&&etaB(C)>2.2))){const pd=nearPad(C);if(pd){ai.mode='pad';ai.tx=pd.x;ai.tz=pd.z;ai.ty=0;return}}
 if(role=='sup'){ai.tx=cl(b.x*.4+(o.idx%2?9:-9),HX-8);ai.tz=cl(b.z+og*16,HZ-8);ai.ty=0;return}
 if(role!='atk'){ai.tx=cl(b.x*.45,role=='sh'?HX-8:6);ai.tz=role=='sh'?og*(HZ-14)+(b.z-og*(HZ-14))*.22:og*(HZ-9);ai.ty=0;return}
 // ----- attacker: find where the ball can be reached, then line up a hit towards the goal -----
 let k=null,aer=false;const sp=(C.boost>8?19:14)*D.sp;
 for(const pk of pred){const dist=Math.hypot(pk.x-C.p.x,pk.z-C.p.z);
  if(pk.y<=2.4){if(dist/sp<=pk.t+.15){k=pk;break}}
  else if(D.ae>=pk.y&&C.boost>30&&pk.t>.9&&dist<30&&.75+pk.y*.12+dist/26<=pk.t){k=pk;aer=true;break}}
 if(!k){const tt=Math.hypot(b.x-C.p.x,b.z-C.p.z)/sp;k=pred[Math.min(pred.length-1,Math.max(0,Math.round(tt/.1)-1))]}
 ai.kx=k.x;ai.ky=k.y;ai.kz=k.z;
 if(aer&&!C.isAir){ai.aer=true;ai.ta=k.t;ai.tx=k.x;ai.tz=k.z;ai.ty=k.y;return}
 const dgr=Math.sign(k.z)==og&&Math.abs(k.z-og*HZ)<34;let ax,az;
 if(dgr){ax=k.x>0?-30:30;az=k.z-og*30}else{ax=(k.x>0?-1:1)*(D.er<1?2:0);az=gz}
 let ux=ax-k.x,uz=az-k.z;const ul=Math.hypot(ux,uz)||1;ux/=ul;uz/=ul;
 const cx=C.p.x-k.x,cz=C.p.z-k.z,dist=Math.hypot(cx,cz),beh=cx*ux+cz*uz;
 if(beh<-1||dist<3.5){ai.tx=k.x-ux*.25;ai.tz=k.z-uz*.25}
 else{const sg=Math.sign(cx*-uz+cz*ux)||1;let d=6,wx,wz;for(;d>=2;d-=1){wx=k.x-ux*d-uz*sg*d*.7;wz=k.z-uz*d+ux*sg*d*.7;if(Math.abs(wx)<HX-3&&Math.abs(wz)<HZ-3)break}ai.tx=wx;ai.tz=wz}
 ai.tx=cl(ai.tx+er(),HX-2);ai.tz=cl(ai.tz+er(),HZ-2);ai.ty=k.y}
function aimAir(Dv,I,up,fwd,rt){I.thr=-cl(Dv.dot(up)*3,1);I.st=-cl(Dv.dot(rt)*3,1);if(Dv.dot(fwd)<-.3)I.thr=-1}
function airLevel(C,I,up,fwd,rt){let tn=V(0,1,0);if(depth(C.p)<7){const nn=normal(C.p);if(nn.y>-.3)tn=nn}I.thr=cl(tn.dot(fwd)*2.5,1);I.roll=cl(tn.dot(rt)*2.5,1);if(up.dot(tn)<-.5){I.roll=1;I.thr=0}}
function drive(o,D,ko,dt){const C=o.C,ai=o.ai,I=o.I,pp=C.p;I.thr=I.st=I.roll=I.sl=I.bo=I.jump=0;ai.cd-=dt;ai.fr++;ai.ta-=dt;
 const up=V(0,1,0).applyQuaternion(C.q),fwd=V(0,0,-1).applyQuaternion(C.q),rt=V(1,0,0).applyQuaternion(C.q),cur=C.v.dot(fwd),spd=C.v.length();
 if(ai.act){ai.at+=dt;const a=ai.at;
  if(ai.act=='flip'){I.thr=1;I.st=ai.fs;I.jump=(a<.1||(a>=.17&&a<.24))?1:0;I.bo=C.boost>5?1:0;if(a>.65){ai.act=null;ai.cd=1.2}return}
  if(ai.act=='back'){I.thr=-1;I.st=ai.fs;if(a>.7){ai.act=null;ai.cd=1}return}
  if(ai.act=='aer'){const T2=Math.max(.12,ai.ta),k=pred[Math.min(pred.length-1,Math.max(0,Math.round(ai.ta/.1)-1))]||{x:b.x,y:b.y,z:b.z};
   I.jump=(a<.2||(a>=.28&&a<.36))?1:0;
   if(!(a>=.28&&a<.36)&&a>=.1){const need=V(k.x-pp.x-C.v.x*T2,k.y-pp.y-C.v.y*T2,k.z-pp.z-C.v.z*T2).multiplyScalar(2/(T2*T2));need.y+=6.5;const Dd=need.clone().normalize();aimAir(Dd,I,up,fwd,rt);if(fwd.dot(Dd)>.8&&C.boost>0&&need.length()>3)I.bo=1}
   if(ai.ta<-.4||(a>.5&&!C.isAir)||(C.boost<=0&&a>1.2)){ai.act=null;ai.cd=.9}
   return}}
 if(C.isAir){airLevel(C,I,up,fwd,rt);if(C.restT>.2){I.thr=0;I.roll=0;I.jump=ai.fr&1}return}   // wheels back down; if stuck on the roof, flip over
 const dd=V(ai.tx-pp.x,ai.ty-pp.y,ai.tz-pp.z);if(ai.mode!='atk')dd.y=0;dd.addScaledVector(up,-dd.dot(up));const L=dd.length()+1e-4;
 const ang=Math.atan2(dd.dot(rt),dd.dot(fwd));I.st=cl(-ang*3,1);
 const cap=23*D.sp;let ws=cap;if(ai.mode=='sup'||ai.mode=='gk'||ai.mode=='sh')ws=L<2?0:Math.min(cap,3+L*1.5);
 I.thr=cur<ws-1?1:(cur>ws+2.5?-1:0);
 if(Math.abs(ang)>1.7&&L>3){I.thr=1;I.sl=1}else if(Math.abs(ang)>.9&&cur>10&&L>6)I.sl=1;
 if(ai.bo&&C.boost>6&&Math.abs(ang)<.25&&cur<22.4&&L>(ai.mode=='atk'?7:18)&&!(ai.mis>0)&&ai.mode!='gk')I.bo=1;
 if(ai.mis>0){ai.mis-=dt;I.thr*=.4}
 if(ai.mode=='atk'&&!ai.aer&&ai.fl&&ai.cd<=0){const bx0=b.x-pp.x,by0=b.y-pp.y,bz0=b.z-pp.z,dB=Math.hypot(bx0,by0,bz0),ab=Math.atan2(bx0*rt.x+by0*rt.y+bz0*rt.z,bx0*fwd.x+by0*fwd.y+bz0*fwd.z);
  if(dB<(ko?5.6:3.4)+.13*Math.max(0,cur)&&b.y<2.4&&Math.abs(ab)<.4&&cur>(ko?10:7)){ai.act='flip';ai.at=0;ai.fs=0}}
 if(ai.aer&&ai.mode=='atk'&&ai.ta<=.85+ai.ky*.12&&C.boost>25){ai.act='aer';ai.at=0}
 if(spd<1.2&&L>5){ai.stk+=dt;if(ai.stk>1.1){ai.stk=0;ai.act='back';ai.at=0;ai.fs=Math.random()<.5?1:-1}}else ai.stk=0}
// 3D bumps between all cars (position push + a little bounce). A supersonic car that hits an enemy demolishes it.
function carCars(){const A=[];for(const o of bots)if(!(o.C.dead>0))A.push({p:o.C.p,v:o.C.v,t:o.t,H:o.C,o});
 const kills=[];const isSS=(e,sp)=>(e.H.ss=e.H.ss?sp>=SS_OFF:sp>=SS_ON)&&!e.H.isAir;   // same rule as the trail: on at 22, off below 21
 
 for(let i=0;i<A.length;i++)for(let j=i+1;j<A.length;j++){const a=A[i],c=A[j],dx=c.p.x-a.p.x,dy=c.p.y-a.p.y,dz=c.p.z-a.p.z,d=Math.hypot(dx,dy,dz);
  if(d<1.35&&d>1e-4){const nx=dx/d,ny=dy/d,nz=dz/d;
   if(a.t!=c.t){const sa=a.v.length(),sc=c.v.length(),aa=isSS(a,sa)&&(a.v.x*nx+a.v.y*ny+a.v.z*nz)>sa*.45,cc=isSS(c,sc)&&-(c.v.x*nx+c.v.y*ny+c.v.z*nz)>sc*.45;
    if(aa)kills.push([c,a]);if(cc)kills.push([a,c]);if(aa||cc)continue}
   const pen=(1.35-d)/2;a.p.x-=nx*pen;a.p.y-=ny*pen;a.p.z-=nz*pen;c.p.x+=nx*pen;c.p.y+=ny*pen;c.p.z+=nz*pen;
   const rel=(c.v.x-a.v.x)*nx+(c.v.y-a.v.y)*ny+(c.v.z-a.v.z)*nz;if(rel<0){if(rel<-3){const nw=performance.now();if(nw-lastBump>120){lastBump=nw;sfxAt('bump',a.p,Math.min(1,-rel/15))}}const j2=-(1.35)*rel/2;a.v.x-=nx*j2;a.v.y-=ny*j2;a.v.z-=nz*j2;c.v.x+=nx*j2;c.v.y+=ny*j2;c.v.z+=nz*j2}}}
 for(const[vic,att]of kills)if(!(vic.H.dead>0))demoCar(vic,att)}
// ---------- demolitions ----------
const DS=[[-32,-44],[-24,-45],[-16,-45],[16,-45],[24,-45],[32,-44]];
function demoCar(vic,att){const H=vic.H,P=vic.p;H.dead=2;
 emitEv([['m',+P.x.toFixed(2),+P.y.toFixed(2),+P.z.toFixed(2),vic.t,+att.v.x.toFixed(1),+att.v.y.toFixed(1),+att.v.z.toFixed(1)]]);
 sfxAt('demo',P,1);vic.v.set(0,0,0);H.isBoost=false;
 const as=att.H.st,vs=H.st;if(as){as.demos++;if(as.demos==7)award(as,20,'EXTERMINATION')}
 if(as&&vs)killAdd(as,vs)}
function dSpot(t){const L=DS.slice().sort(()=>Math.random()-.5),alive=[];for(const o of bots)if(!(o.C.dead>0))alive.push(o.C.p);
 const sp=k=>[t?-k[0]:k[0],t?-k[1]:k[1]];
 for(const k of L){const[x,z]=sp(k);if(alive.every(a=>Math.hypot(a.x-x,a.z-z)>5))return[x,z]}
 return sp(L[0])}
function respawnBot(o){sfxAt('spawn',o.C.p,.6);const[x,z]=dSpot(o.t),st=o.st,t=o.t;o.C=mkS(x,z,Math.atan2(x,z));o.C.t=t;o.C.st=st;const a=o.ai;a.act=null;a.rt=0;a.cd=0;a.mis=0;a.stk=0}
function demoTick(dt){for(const o of bots)if(o.C.dead>0){o.C.dead-=dt;if(o.C.dead<=0){o.C.dead=0;respawnBot(o)}}}

// ---------- scoring ----------
// called on every car->ball hit (after the hit impulse has been applied to bv)
function onTouch(H,cq){const st=H.st;if(!st)return;const t=H.t,og=t?-HZ:HZ,sg=Math.sign(og),own=-og;
 if(koFirst)koFirst=false;else if(simT-st.tT>.5)award(st,2,'BALL TOUCH');   // first touch of a kickoff = 0, rapid hits = 2 total
 st.tT=simT;
 const air=H.isAir,fw=V(0,0,-1).applyQuaternion(cq),upv=V(0,1,0).applyQuaternion(cq),dz=og-b.z,sp=bv.length();
 if(!lastTc||lastTc.st!==st){prevTc=lastTc;lastTc={st:st,t:t,at:simT,mods:[]}}else lastTc.at=simT;
 const mods=[];if(air&&b.y>2.4)mods.push('AERIAL');if(air&&upv.y<-.3)mods.push('TURTLE');if(fw.z*sg<-.35)mods.push('BACKWARDS');if(Math.abs(dz)>=60)mods.push('LONG');lastTc.mods=mods;
 if(pend&&pend.team!==t&&simT-pend.at<8){const epic=Math.abs(b.z-own)<12;st.saves++;award(st,epic?75:50,epic?'EPIC SAVE':'SAVE');if(st.saves==3)award(st,25,'SAVIOR');pend=null}
 else if(pend&&pend.team===t)pend=null;
 let shot=false;
 if(sp>8&&bv.z*sg>3){const tt=dz/bv.z,gx=b.x+bv.x*tt,gy=b.y+bv.y*tt-3.25*tt*tt;shot=tt>0&&tt<5&&Math.abs(gx)<GW+1.5&&gy<GH+1.5&&gy>-.5}
 if(shot){st.shots++;award(st,10,'SHOT ON GOAL');pend={team:t,at:simT}}
 else if(Math.abs(dz)<30&&Math.abs(b.x)>6&&sp>8&&bv.x*Math.sign(b.x)<-4&&bv.z*sg>-2)award(st,10,'CENTER BALL');
 if(Math.abs(b.z-own)<28&&bv.z*sg>6&&sp>10)award(st,20,'CLEAR BALL')}
function onGoal(gt){pend=null;goalInfo={team:gt,st:null,as:null};const s=lastTc&&lastTc.t==gt?lastTc:null;if(!s)return;const st=s.st;goalInfo.st=st;
 award(st,100,'GOAL');st.goals++;for(const m of s.mods)award(st,20,m+' GOAL');
 if(ot)award(st,25,'OVERTIME GOAL');if(st.goals==3)award(st,25,'HAT TRICK');
 if(prevTc&&prevTc.t==gt&&prevTc.st!==st&&s.at-prevTc.at<5){const a=prevTc.st;goalInfo.as=a;a.assists++;award(a,50,'ASSIST');if(a.assists==3)award(a,25,'PLAYMAKER')}}

// ---------- car + ball physics ----------
const rotWq=(q,vec,dt)=>{const l=vec.length();if(l>1e-4)q.premultiply(new T.Quaternion().setFromAxisAngle(vec.clone().divideScalar(l),l*dt))};
const needDq=(q,nn,uu)=>{const l=nn.clone().applyQuaternion(q.clone().invert()),un=uu.dot(nn);return Math.max(.42*Math.abs(l.x)+HB_HH*Math.abs(l.y)+.59*Math.abs(l.z)-HB_CY*un,RH*Math.max(0,un))};
// bots use the exact same car physics as the player (generated from step2)
function carStep(C,I,dt){const p=C.p,v=C.v,q=C.q,w=C.w,dodgeW=C.dodgeW;let{boost,isAir,isBoost,airT,restT,jumpT,dodgeT,ceilT,jcool,jprev,hasJump,dodged,selfFlip,dFw,dRt}=C;
 const up=V(0,1,0).applyQuaternion(q),fwd=V(0,0,-1).applyQuaternion(q),rt=V(1,0,0).applyQuaternion(q);
 const d=depth(p);normal(p,n);
 const thr=I.thr,st=I.st,roll=I.roll,
 sl=I.sl,bo=I.bo&&boost>0,jump=I.jump,jp=jump&&!jprev;jprev=jump;isBoost=bo;jcool-=dt;
 const upn=up.dot(n);
 // wheels only count as "on the ground" when they actually face the surface (no more auto-righting)
 const nd0=needDq(q,n,up);   // how far the hitbox reaches toward this surface
 let ground=d<Math.max(.45,nd0+.07)&&jcool<=0&&dodgeT<=0&&upn>.6&&v.dot(n)<2&&(n.y>.6||thr!==0||bo);   // a tilted car whose nose/corner touches the floor still counts as grounded -> it snaps flat instead of balancing on the corner
 if(ground&&n.y<-.3&&(v.length()<4||ceilT>.9))ground=false;
 if(ground&&jp){v.addScaledVector(up,3);jumpT=.2;jcool=.1;hasJump=true;airT=0;ground=false}isAir=!ground;
 const touching=!ground&&d<needDq(q,n,up)+.1;
 if(ground){
  airT=0;hasJump=true;dodgeT=0;dodged=false;selfFlip=false;restT=0;w.set(0,0,0);if(n.y<-.3)ceilT+=dt;else if(n.y>-.1)ceilT=0;
  const al=new T.Quaternion().setFromUnitVectors(up,n);q.premultiply(new T.Quaternion().slerp(al,1-Math.exp(-(nd0>d+.01&&nd0>.3?42:16)*dt)));
  up.set(0,1,0).applyQuaternion(q);fwd.set(0,0,-1).applyQuaternion(q);rt.set(1,0,0).applyQuaternion(q);
  const vf=v.dot(fwd),vl=v.dot(rt);let acc=0;
  if(thr>0)acc=vf<-.3?35:16*Math.max(0,1-vf/MAXV);else if(thr<0)acc=vf>.3?-35:-16*Math.max(0,1+vf/MAXV);else if(!bo)acc=-Math.sign(vf)*Math.min(5,Math.abs(vf)/dt);
  if(bo)acc+=9.92;if(sl)acc-=Math.sign(vf)*3;
  v.addScaledVector(fwd,acc*dt);v.addScaledVector(rt,-vl*(1-Math.exp(-(sl?1.3:26)*dt)));
  const sp=Math.hypot(vf,vl),k=1.25/(1+Math.pow(sp/3,1.2))*(sl?1.6:1),yaw=Math.max(-7,Math.min(7,st*k*sp*(vf<-.5?-1:1)));
  q.premultiply(new T.Quaternion().setFromAxisAngle(up,yaw*dt));
  if(v.length()>23)v.setLength(23);
  v.addScaledVector(n,-v.dot(n));p.addScaledVector(v,dt);
  const d2=depth(p);normal(p,n2);p.addScaledVector(n2,Math.max(RH,needDq(q,n2,up))-d2);
 }else{
  airT+=dt;
  // resting on a surface (roof / side / sitting on a wall) refills the jump & flip
  if(touching){restT+=dt;if(restT>.15&&dodgeT<=0){airT=0;hasJump=true;if(dodged){dodged=false;w.set(0,0,0)}}}else restT=0;
  const onSurf=touching&&restT>.1&&dodgeT<=0;
  if(jp&&onSurf&&upn>.6&&jcool<=0){v.addScaledVector(up,3);jumpT=.2;jcool=.1;hasJump=true;airT=0}   // normal jump from wheels that are resting on a wall
  else if(jump&&jumpT>0){v.addScaledVector(up,14.58*dt);jumpT-=dt}else jumpT=0;
  if(jp&&hasJump&&jcool<=0&&airT<1.25&&dodgeT<=0){
   hasJump=false;const rolled=touching&&upn<.5,inp=thr!==0||st!==0;
   let dd=fwd.clone().multiplyScalar(thr).addScaledVector(rt,-st);
   if(rolled){ // on roof / side: hop and flip back over
    if(!inp){let bd=-9;for(const c of[rt,rt.clone().negate(),fwd,fwd.clone().negate()]){const dv=c.dot(n);if(dv>bd+1e-6){bd=dv;dd.copy(c)}}}else dd.normalize();
    v.addScaledVector(n,3);if(inp)v.addScaledVector(dd.clone().addScaledVector(n,-dd.dot(n)),4);
    dodgeT=.5;dodged=true;selfFlip=true;w.set(0,0,0);dodgeW.crossVectors(up,dd).multiplyScalar(12.57)}
   else if(!inp)v.addScaledVector(up,3);
   else{dd.normalize();const fw=dd.dot(fwd),imp=5*(1+(fw>0?.9*fw*Math.min(1,Math.max(0,v.dot(fwd))/23):0));
    v.addScaledVector(dd,imp);dodgeT=.5;dodged=true;selfFlip=false;w.set(0,0,0);{const il=Math.hypot(thr,st)||1;dFw=thr/il;dRt=-st/il}dodgeW.crossVectors(up,dd).multiplyScalar(12.57)}}
  if(dodgeT>0){dodgeT-=dt;let f=1;
   if(!selfFlip){const opp=Math.max(0,Math.min(1,-(dFw*thr+dRt*(-st))));f=Math.max(0,1-2*opp);   // flip cancel: hold the opposite direction and the flip stops
    if(f<=0&&dodgeT<.46){dodgeT=0;w.set(0,0,0)}}
   rotWq(q,dodgeW.clone().multiplyScalar(f),dt);if(selfFlip&&V(0,1,0).applyQuaternion(q).dot(n)>.98){dodgeT=0;dodged=false;selfFlip=false;w.set(0,0,0)}}
  else if(touching&&upn<.6){w.set(0,0,0)}   // lying on side / roof: air control is off, so no cartwheeling
  else{const rl=sl?Math.max(-1,Math.min(1,roll-st)):roll,yw=sl?0:st,tg=rt.clone().multiplyScalar(-thr*5.5).addScaledVector(up,yw*4.5).addScaledVector(fwd,rl*5.5);w.lerp(tg,1-Math.exp(-7*dt));rotWq(q,w,dt)}   // flip over (dodgeT<=0): control comes back
  if(bo)v.addScaledVector(fwd,9.92*dt);
  v.y-=6.5*dt;if(v.length()>23)v.setLength(23);p.addScaledVector(v,dt);
  // world contact: box support function, so the car lands / rests on whatever part touches first
  const d2=depth(p);normal(p,n2);const uc=V(0,1,0).applyQuaternion(q),nd2=needDq(q,n2,uc);
  if(d2<nd2){p.addScaledVector(n2,nd2-d2);const vn=v.dot(n2);if(vn<0)v.addScaledVector(n2,-vn*(vn<-3?1.1:1))}
  if(d2<nd2+.05){
   const un=uc.dot(n2);
   if(un<.6){const tv=v.clone().addScaledVector(n2,-v.dot(n2)),ts=tv.length();if(ts>1e-4)v.addScaledVector(tv,-Math.min(1,6*dt/ts))} // roof/side friction
   // gently topple to the nearest resting pose (roof stays on roof) - only if the player isn't steering and not mid-flip
   if(dodgeT<=0&&jcool<=0&&Math.abs(un)<.9995){
    const ta=un>=0?n2:n2.clone().negate();
    q.premultiply(new T.Quaternion().slerp(new T.Quaternion().setFromUnitVectors(uc,ta),1-Math.exp(-(un>=0?5:6)*dt)))}
  }
 }
 if(bo)boost=Math.max(0,boost-BOOST_DRAIN*dt);C.boost=boost;C.isAir=isAir;C.isBoost=isBoost;C.airT=airT;C.restT=restT;C.jumpT=jumpT;C.dodgeT=dodgeT;C.ceilT=ceilT;C.jcool=jcool;C.jprev=jprev;C.hasJump=hasJump;C.dodged=dodged;C.selfFlip=selfFlip;C.dFw=dFw;C.dRt=dRt}
function ballWorld(dt){ // ball vs arena: bounce (e=.6), and Coulomb friction on the contact point so it rolls instead of braking
 const d=depth(b);if(d>BR-1e-3)return;
 normal(b,nb);b.addScaledVector(nb,BR-d);
 const vn=bv.dot(nb);let jn=0;
 if(vn<0){const e=Math.abs(vn)<1.5?.15:.6;jn=-(1+e)*vn;bv.addScaledVector(nb,jn);if(jn>4){const nw=performance.now();if(nw-lastBnc>90){lastBnc=nw;sfxAt('bounce',b,Math.min(1,jn/25))}}}
 const r=nb.clone().multiplyScalar(-BR),vc=bv.clone().add(bw.clone().cross(r));vc.addScaledVector(nb,-vc.dot(nb));
 const sl=vc.length();
 if(sl>1e-5){const j=Math.min(sl/3.5,.35*(jn+6.5*dt*Math.max(0,nb.y)));vc.multiplyScalar(-j/sl);bv.add(vc);bw.add(r.clone().cross(vc).multiplyScalar(1/(.4*BR*BR)))}
 if(nb.y>.5)bv.multiplyScalar(1-.04*dt)}
function carBallHit(p,q,v,H){if(H.dead>0)return;const lp=b.clone().sub(p).applyQuaternion(q.clone().invert());lp.y-=HB_CY;
 const cp=V(cl(lp.x,.42),cl(lp.y,HB_HH),cl(lp.z,.59)),dl=lp.clone().sub(cp),dist=dl.length();
 if(dist<BR){const nw=(dist>1e-5?dl.divideScalar(dist):V(0,1,0)).applyQuaternion(q);b.addScaledVector(nw,BR-dist);
  const vn=bv.clone().sub(v).dot(nw);if(vn<0){const rs=Math.min(bv.clone().sub(v).length(),60),j=-vn/(1/30+1/180);bv.addScaledVector(nw,j/30);v.addScaledVector(nw,-j/180);
  if(H.hc<=0){H.hc=.1;lastHitT=simT;hitT[H.t]=simT;
   // Rocket League style extra impulse: direction from car centre (up squashed to .35, forward to .65), strength falls off with closing speed
   const rl=b.clone().sub(p).applyQuaternion(q.clone().invert());rl.y=(rl.y-HB_CY)*.35;rl.z*=.65;
   const hd=rl.lengthSq()>1e-6?rl.normalize().applyQuaternion(q):nw.clone();
   const m=rs<5?.65:rs<23?.65-.10*(rs-5)/18:rs<46?.55-.25*(rs-23)/23:.30;
   bv.addScaledVector(hd,rs*m);sfxAt('hit',b,Math.max(.25,Math.min(1,bv.length()/40)));onTouch(H,q)}}}}
function ballStep(dt){
 if(phase!=0)return;
 for(const o of bots)o.C.hc-=dt;bv.y-=6.5*dt;bv.multiplyScalar(1-.03*dt);if(bv.length()>60)bv.setLength(60);b.addScaledVector(bv,dt);
 ballWorld(dt);
 for(const o of bots)carBallHit(o.C.p,o.C.q,o.C.v,o.C);
 ballWorld(dt);   // after the car, so a ball pushed into a wall/floor is put back out
 if(bw.length()>70)bw.setLength(70);const sw=bw.length();if(sw>.01)bq.premultiply(new T.Quaternion().setFromAxisAngle(bw.clone().divideScalar(sw),sw*dt));
 if(Math.abs(b.z)>HZ+BR&&Math.abs(b.x)<GW&&b.y<GH){score[b.z>0?0:1]++;goalT=GOAL_T;phase=1;goalAt=simT;goalTeam=b.z>0?0:1;onGoal(goalTeam);if(hitT[goalTeam]>=0)lastHitT=hitT[goalTeam];goalPos.copy(b);ballVisible=false;explode(goalPos,goalTeam);goalBlast()}}


// the goal explosion throws every car away from the goal (same as the old host-side behaviour for the local player)
function goalBlast(){for(const o of bots){const C=o.C;if(C.dead>0)continue;const d=C.p.clone().sub(goalPos),dist=d.length(),f=Math.max(0,1-dist/45);if(f<=0)continue;
 d.y=0;if(d.lengthSq()<1e-4)d.set(0,0,-goalPos.z);d.normalize();C.v.addScaledVector(d,6+34*f);C.v.y+=3+9*f;C.jcool=.5;C.w.add(V((Math.random()-.5)*6*f,(Math.random()-.5)*4*f,(Math.random()-.5)*6*f))}}

function padsUpdate(dt){for(const a of pads){if(a.t>0){a.t-=dt;continue}const r2=(a.big?2.6:1.7)**2;
 for(const o of bots){const C=o.C,dx=C.p.x-a.x,dz=C.p.z-a.z;
  if(dx*dx+dz*dz<r2&&C.p.y<1.5&&!(C.dead>0)){C.boost=Math.min(100,C.boost+(a.big?100:12));a.t=a.big?10:4;sfxAt(a.big?'padBig':'pad',{x:a.x,y:.04,z:a.z},.5);break}}}}

// ---------- kickoff / clock / end of match ----------
function kickSetup(){koIdx.sort(()=>Math.random()-.5);const cnt=[0,0];
 for(const o of bots){const t=o.t,i=Math.min(cnt[t]++,4),k=KP[koIdx[i]],x=t?-k[0]:k[0],z=t?-k[1]:k[1],yaw=Math.atan2(x,z),st=o.st;
  o.C=mkS(x,z,yaw);o.C.t=t;o.C.st=st;o.ai.act=null;o.ai.rt=0;o.ai.cd=0;o.ai.mis=0;o.ai.stk=0}
 cdT=3.2+(firstKo?2:0);firstKo=false;goT=0}
function resetAll(){
 if(!matchEnd&&score[0]!=score[1]&&(ot||mTime<=0)){endMatch();return}
 tUp=0;koFirst=true;lastTc=prevTc=pend=null;hitT[0]=hitT[1]=-1;b.set(0,BR,0);bv.set(0,0,0);bw.set(0,0,0);goalT=0;phase=0;lastHitT=-1;ballVisible=true;hist.length=0;cdT=0;goT=0;kickSetup()}
function clockStep(dt){if(phase!=0||cdT>0||matchEnd)return;
 if(ot){otT+=dt;return}
 mTime=Math.max(0,mTime-dt);{const k=Math.ceil(mTime);if(k!=lastSec){lastSec=k;if(k<=5&&k>0)emitEv([['t','tick2']])}}
 if(mTime<=0){tUp+=dt;if(b.y<BR+.25||tUp>7){if(score[0]!=score[1])endMatch();else{ot=true;otT=0;resetAll()}}}}
function endMatch(){matchEnd=true;phase=0;const wt=score[0]>score[1]?0:1;let best=null;
 for(const o of bots){const x=o.st;if(x.t==wt&&(!best||x.score>best.score))best=x}
 if(best){best.score+=50;best.mvp=1}}
function cdUpd(dt){cdT-=dt;if(cdT>0)return;cdT=0;goT=.8}

// ---------- instant replay (the server records the match, then plays the last goal back to everybody) ----------
const vtmp=V(0,0,0),qtmp=new T.Quaternion();
function snapH(){hist.push({t:simT,b:b.toArray(),bq:bq.toArray(),bt:bots.map(o=>{const C=o.C;return[o.id,C.p.x,C.p.y,C.p.z,C.q.x,C.q.y,C.q.z,C.q.w,C.isBoost?1:0,C.dead>0?1:0,C.v.x,C.v.y,C.v.z]})});
 while(hist.length&&hist[0].t<simT-15)hist.shift()}
function sample(t){let i=Math.min(rIdx,hist.length-2);while(i<hist.length-2&&hist[i+1].t<t)i++;rIdx=i;
 const A=hist[i],B=hist[i+1],f=B.t>A.t?Math.max(0,Math.min(1,(t-A.t)/(B.t-A.t))):0;
 b.fromArray(A.b).lerp(vtmp.fromArray(B.b),f);bq.fromArray(A.bq).slerp(qtmp.fromArray(B.bq),f);
 const bm=new Map();for(const e of B.bt)bm.set(e[0],e);
 for(const a of A.bt){const c=bm.get(a[0]),o=bots.find(x=>x.id===a[0]);if(!o||!c)continue;const C=o.C;
  C.p.set(a[1],a[2],a[3]).lerp(vtmp.set(c[1],c[2],c[3]),f);C.q.set(a[4],a[5],a[6],a[7]).slerp(qtmp.set(c[4],c[5],c[6],c[7]),f);C.isBoost=!!a[8];C.dead=a[9]?1:0;C.v.set(a[10],a[11],a[12])}}
function rSpeed(t){if(lastHitT<0)return 1;const A=lastHitT-.2,B=lastHitT+.6,d=t<A?A-t:t>B?t-B:0,f=1-Math.min(1,d/.4),s=f*f*(3-2*f);return 1-.8*s}
function startReplay(){if(hist.length<3){resetAll();return}
 const t0=hist[0].t;let s=goalAt-8;if(lastHitT>=t0)s=Math.min(s,lastHitT-2);s=Math.max(t0,s,goalAt-10);
 rt=s;rIdx=0;while(rIdx<hist.length-2&&hist[rIdx+1].t<s)rIdx++;
 phase=2;sample(rt);ballVisible=true}
function replayStep(dt){const prev=rt;rt+=dt*rSpeed(rt);if(rt>=hist[hist.length-1].t){resetAll();return}
 sample(rt);ballVisible=rt<goalAt;if(prev<goalAt&&rt>=goalAt)explode(goalPos,goalTeam)}

// ---------- public API ----------
const cn1=x=>Math.max(-1,Math.min(1,+x||0));
function input(id,a){const o=bots.find(x=>x.id===id);if(!o||!o.pl||!Array.isArray(a))return;const I=o.I;
 I.thr=cn1(a[0]);I.st=cn1(a[1]);I.roll=cn1(a[2]);I.sl=a[3]?1:0;I.bo=a[4]?1:0;I.jr=a[5]?1:0;if(I.jr)o.jh=.05}
function start(players,cfg){
 bots.length=0;lenSec=cfg.len||120;mDiff=cfg.diff==null?1:Math.max(0,Math.min(2,cfg.diff|0));
 const cnt=[0,0];for(const pl of players){const o=addCar(pl);o.idx=cnt[pl.team]++}
 score=[0,0];mTime=lenSec;ot=false;otT=0;matchEnd=false;tUp=0;firstKo=true;phase=0;simT=0;seq=0;lastSec=0;for(const a of pads)a.t=0;resetAll()}
function rematch(){
 matchEnd=false;score=[0,0];mTime=lenSec;ot=false;otT=0;tUp=0;firstKo=true;phase=0;lastSec=0;
 for(const o of bots){const sub=o.st.sub;o.st=mkSt(o.name,o.t,sub);o.st.nid=o.id;o.C.st=o.st}
 for(const a of pads)a.t=0;resetAll();emitEv([['rm']])}
function removeCar(id){const i=bots.findIndex(o=>o.id===id);if(i>=0)bots.splice(i,1)}
// one frame of the match (same order of work as the old browser host loop)
function tick(dt){
 if(!matchEnd&&phase!=2){
  if(cdT>0)cdUpd(dt);
  else{
   if(goT>0)goT-=dt;
   for(const o of bots){if(!o.pl)continue;o.jh-=dt;o.I.jump=(o.I.jr||o.jh>0)?1:0}   // humans: keep a jump press alive for one physics tick even if the packet was short
   botsAI(dt,phase==0);
   for(let i=0;i<3;i++){for(const o of bots)if(!(o.C.dead>0))carStep(o.C,o.I,dt/3);ballStep(dt/3);simT+=dt/3}
   carCars();demoTick(dt);padsUpdate(dt);snapH();clockStep(dt);
   if(phase==1){goalT-=dt;if(goalT<=0)startReplay()}}}
 else if(!matchEnd)replayStep(dt)}
function snapshot(){
 const r=(x,k)=>Math.round(x*k)/k,P=(id,pp,qq,vv,fl,bo,dd)=>[id,r(pp.x,100),r(pp.y,100),r(pp.z,100),r(qq.x,1e4),r(qq.y,1e4),r(qq.z,1e4),r(qq.w,1e4),r(vv.x,10),r(vv.y,10),r(vv.z,10),fl,Math.round(bo),dd>0?r(dd,10):0];
 const pl=bots.map(o=>{const C=o.C;return P(o.id,C.p,C.q,C.v,(C.isBoost?1:0)|(C.isAir?2:0),C.boost,C.dead)});
 const S={t:'snap',n:++seq,rh:0,pl:pl,b:[r(b.x,100),r(b.y,100),r(b.z,100),r(bv.x,10),r(bv.y,10),r(bv.z,10),r(bq.x,1e4),r(bq.y,1e4),r(bq.z,1e4),r(bq.w,1e4)],bv:ballVisible?1:0,sc:[score[0],score[1]],mt:r(mTime,10),ot:ot?1:0,oo:r(otT,10),ph:phase,gT:r(goalT,100),gt:goalTeam,cd:r(cdT,100),me:matchEnd?1:0,pd:pads.map(a=>a.t>0?0:1).join('')};
 if(goalInfo)S.gi=[goalInfo.team,goalInfo.st?goalInfo.st.nid:null,goalInfo.as?goalInfo.as.nid:null];
 if(seq%12==0||(matchEnd&&seq%6==0))S.ss=bots.map(o=>o.st).map(s=>[s.nid,s.score,s.goals,s.assists,s.saves,s.shots,s.demos,s.mvp]);
 return S}
function drainEv(){const q=evq;evq=[];return q}
return { start, rematch, removeCar, input, tick, snapshot, drainEv, get matchEnd(){return matchEnd}, get score(){return score}, get cars(){return bots}, get phase(){return phase} };
}
module.exports = { makeSim };
