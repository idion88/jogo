/* server.js — servidor AUTORITÁRIO */
const http=require('http'),fs=require('fs'),path=require('path');
const WebSocket=require('ws');

/* ---- constantes (espelho do index.html) ---- */
const TICK=50, LAPS=3, E=0.35;
const CARS=[
 {max:640,acc:380,grip:5.5,brk:420,turn:2.6,mass:1.00,r:15},
 {max:560,acc:420,grip:7.0,brk:520,turn:2.9,mass:1.05,r:15},
 {max:500,acc:520,grip:8.5,brk:560,turn:3.4,mass:0.90,r:14},
 {max:540,acc:320,grip:6.5,brk:480,turn:2.7,mass:1.60,r:18},
 {max:520,acc:440,grip:10 ,brk:600,turn:3.2,mass:0.95,r:15},
];
const TRACKS=[
 {w:90,p:[[150,150],[1450,150],[1550,250],[1550,750],[1450,850],[150,850],[50,750],[50,250]],
  cps:[[800,150],[1550,500],[800,850],[50,500]]},
 {w:56,p:[[150,150],[650,150],[750,250],[650,350],[350,350],[250,450],[350,550],[750,550],[850,650],[750,750],[150,750],[50,650],[50,250]],
  cps:[[700,200],[300,400],[800,600],[100,500]]},
 {w:70,p:[[150,150],[1450,150],[1550,250],[1550,750],[1450,850],[900,850],[800,750],[700,650],[600,750],[500,850],[150,850],[50,750],[50,250]],
  cps:[[800,150],[1550,500],[900,850],[500,850],[50,500]],
  atalho:{w:30,p:[[900,850],[700,800],[500,850]]}},
];
function stepCar(c,inp,dt,sup){
  const C=CARS[c.car];
  const fX=Math.cos(c.h),fY=Math.sin(c.h),rX=-fY,rY=fX;
  let vf=c.vx*fX+c.vy*fY, vl=c.vx*rX+c.vy*rY;
  if(inp.th>0)vf+=C.acc*inp.th*dt;
  if(inp.br>0)vf-=C.brk*inp.br*dt;
  vf-=vf*(0.4+sup.drag)*dt;  // arrasto: base 0.4 + extra fora da pista
  vl*=Math.max(0,1-C.grip*sup.grip*dt);
  vf=Math.max(-C.max*0.35,Math.min(C.max*sup.cap,vf));
  const eff=Math.min(1,Math.abs(vf)/60)*(vf<0?-1:1);  // limiar reduzido: 60
  c.h+=inp.st*C.turn*eff*dt;
  const nX=Math.cos(c.h),nY=Math.sin(c.h);
  c.vx=nX*vf+(-nY)*vl; c.vy=nY*vf+nX*vl;
  c.x+=c.vx*dt; c.y+=c.vy*dt;
}
function distSeg(px,py,ax,ay,bx,by){const dx=bx-ax,dy=by-ay,L=dx*dx+dy*dy||1;
  let t=((px-ax)*dx+(py-ay)*dy)/L;t=Math.max(0,Math.min(1,t));
  return Math.hypot(px-(ax+dx*t),py-(ay+dy*t));}
function surfaceAt(ti,x,y){
  const T=TRACKS[ti];let d=1e9;
  for(let i=0;i<T.p.length;i++){const a=T.p[i],b=T.p[(i+1)%T.p.length];
    d=Math.min(d,distSeg(x,y,a[0],a[1],b[0],b[1]));}
  if(d<=T.w/2)return{grip:1,cap:1,drag:0,onTrack:true};
  if(T.atalho){let ds=1e9;const S=T.atalho.p;
    for(let i=0;i<S.length-1;i++)ds=Math.min(ds,distSeg(x,y,S[i][0],S[i][1],S[i+1][0],S[i+1][1]));
    if(ds<=T.atalho.w/2)return{grip:.45,cap:1,drag:0,onTrack:true};}
  return{grip:.4,cap:.3,drag:3.5,onTrack:false};  // FORA DA PISTA: punição severa
}

/* ---- salas ---- */
const rooms=new Map();
const CODE='ABCDEFGHJKLMNPQRSTUVWXYZ23456789';
const mkCode=()=>Array.from({length:5},()=>CODE[Math.random()*CODE.length|0]).join('');

function newRoom(host){
  let c; do{c=mkCode();}while(rooms.has(c));
  const r={code:c,players:[],phase:'lobby',track:0,countEnd:0,raceStart:0,rematch:new Set()};
  rooms.set(c,r); r.players.push(host); host.room=r; host.host=true;
  return r;
}
function grid(r){
  const T=TRACKS[r.track],[sx,sy]=T.cps[0];
  r.players.forEach((p,i)=>{
    p.x=sx-60-i*46; p.y=sy+(i%2?-1:1)*T.w*0.18; p.h=0;
    p.vx=0;p.vy=0;p.lap=1;p.nextCp=1;p.fin=false;p.finT=0;
    p.input={th:0,br:0,st:0}; p.lastSeq=0;
  });
}
function sendRoom(p){
  if(!p.room)return;
  p.ws.send(JSON.stringify({t:'room',code:p.room.code,track:p.room.track,
    you:p.id,host:!!p.host,myCar:p.car,meName:p.name,
    players:p.room.players.map(q=>({id:q.id,name:q.name,car:q.car,host:!!q.host}))}));
}
const bcast=r=>r.players.forEach(p=>p.connected&&sendRoom(p));

/* ---- laço autoritário: 20 Hz ---- */
setInterval(()=>{
  const now=Date.now();
  for(const r of rooms.values()){
    if(r.phase==='lobby')continue;
    if(r.phase==='countdown'&&now>=r.countEnd){r.phase='race';r.raceStart=now;}
    if(r.phase==='race'||r.phase==='finished'){
      for(const p of r.players)
        stepCar(p,p.input,TICK/1000,surfaceAt(r.track,p.x,p.y));
      for(let i=0;i<r.players.length;i++)for(let j=i+1;j<r.players.length;j++){
        const a=r.players[i],b=r.players[j];
        const dx=b.x-a.x,dy=b.y-a.y,d=Math.hypot(dx,dy),R=CARS[a.car].r+CARS[b.car].r;
        if(d>0&&d<R){
          const nx=dx/d,ny=dy/d,ov=R-d,ia=1/CARS[a.car].mass,ib=1/CARS[b.car].mass;
          a.x-=nx*ov*ia/(ia+ib);a.y-=ny*ov*ia/(ia+ib);
          b.x+=nx*ov*ib/(ia+ib);b.y+=ny*ov*ib/(ia+ib);
          const rel=(b.vx-a.vx)*nx+(b.vy-a.vy)*ny;
          if(rel<0){const jI=-(1+E)*rel/(ia+ib);
            a.vx-=nx*jI*ia;a.vy-=ny*jI*ia;b.vx+=nx*jI*ib;b.vy+=ny*jI*ib;}
        }
      }
      const T=TRACKS[r.track];
      for(const p of r.players){
        if(p.fin)continue;
        const alvo=(p.nextCp<T.cps.length)?T.cps[p.nextCp]:T.cps[0];
        if(Math.hypot(p.x-alvo[0],p.y-alvo[1])<T.w*0.9+20){
          if(p.nextCp<T.cps.length)p.nextCp++;
          else{p.nextCp=1;p.lap++;
            if(p.lap>LAPS){p.fin=true;p.finT=now;}}
        }
      }
      if(r.players.every(p=>p.fin||p.offline))r.phase='finished';
    }
    const dist=p=>{const a=(p.nextCp<TRACKS[r.track].cps.length)?TRACKS[r.track].cps[p.nextCp]:TRACKS[r.track].cps[0];
      return Math.hypot(p.x-a[0],p.y-a[1]);};
    r.order=r.players.slice().sort((a,b)=>{
      if(a.fin&&b.fin)return a.finT-b.finT;
      if(a.fin!==b.fin)return a.fin?-1:1;
      if(b.lap!==a.lap)return b.lap-a.lap;
      if(b.nextCp!==a.nextCp)return b.nextCp-a.nextCp;
      return dist(a)-dist(b);
    }).map(p=>p.id);
    const msg=JSON.stringify({t:'state',sT:now,phase:r.phase,countEnd:r.countEnd,
      raceStart:r.raceStart,order:r.order,
      lastSeqs:Object.fromEntries(r.players.map(p=>[p.id,p.lastSeq])),
      cars:r.players.map(p=>({id:p.id,name:p.name,car:p.car,x:Math.round(p.x),y:Math.round(p.y),
        h:+p.h.toFixed(3),vx:Math.round(p.vx),vy:Math.round(p.vy),lap:p.lap,
        fin:p.fin,finT:p.finT,off:p.offline}))});
    r.players.forEach(p=>{if(p.connected)p.ws.send(msg);});
  }
},TICK);

/* ---- conexão ---- */
const srv=http.createServer((q,s)=>{
  if(q.url==='/'||q.url==='/index.html'){s.writeHead(200,{'Content-Type':'text/html'});
    s.end(fs.readFileSync(path.join(__dirname,'index.html')));}
  else{s.writeHead(404);s.end();}
});
const wss=new WebSocket.Server({server:srv});
wss.on('connection',ws=>{
  const p={ws,id:Math.random().toString(36).slice(2,8),name:'',car:1,room:null,
    host:false,connected:true,offline:false,x:0,y:0,h:0,vx:0,vy:0,
    lap:1,nextCp:1,fin:false,finT:0,input:{th:0,br:0,st:0},lastSeq:0};
  ws.on('message',d=>{
    const m=JSON.parse(d);
    if(m.t==='create'){p.name=String(m.name).slice(0,12);newRoom(p);sendRoom(p);}
    else if(m.t==='join'){
      const r=rooms.get(String(m.code).toUpperCase());
      if(!r)return ws.send(JSON.stringify({t:'err',msg:'Sala não encontrada'}));
      if(r.phase!=='lobby')return ws.send(JSON.stringify({t:'err',msg:'Corrida em andamento'}));
      if(r.players.length>=6)return ws.send(JSON.stringify({t:'err',msg:'Sala cheia (máx. 6)'}));
      p.name=String(m.name).slice(0,12);p.room=r;r.players.push(p);bcast(r);
    }
    else if(m.t==='car'&&p.room){p.car=Math.max(0,Math.min(4,m.car|0));bcast(p.room);}
    else if(m.t==='track'&&p.room&&p.host){p.room.track=Math.max(0,Math.min(2,m.track|0));bcast(p.room);}
    else if(m.t==='start'&&p.room&&p.host&&p.room.phase==='lobby'&&p.room.players.length>=2){
      grid(p.room);p.room.phase='countdown';p.room.countEnd=Date.now()+3000;p.room.rematch.clear();bcast(p.room);}
    else if(m.t==='rematch'&&p.room&&p.room.phase!=='lobby'){
      p.room.rematch.add(p.id);
      const todos=p.room.players.filter(q=>q.connected).every(q=>p.room.rematch.has(q.id));
      if(todos){grid(p.room);p.room.phase='countdown';p.room.countEnd=Date.now()+3000;p.room.rematch.clear();}
    }
    else if(m.t==='input'&&p.room){
      p.input={th:+m.th||0,br:+m.br||0,st:Math.max(-1,Math.min(1,+m.st||0))};
      p.lastSeq=m.seq;
    }
  });
  ws.on('close',()=>{
    p.connected=false;
    if(p.room){
      if(p.room.phase==='lobby'){p.room.players=p.room.players.filter(q=>q!==p);bcast(p.room);}
      else{p.offline=true;p.input={th:0,br:0,st:0};}
    }
  });
});
const PORT = process.env.PORT || 8080;
srv.listen(PORT,()=>console.log('Corrida no ar: http://localhost:'+PORT));