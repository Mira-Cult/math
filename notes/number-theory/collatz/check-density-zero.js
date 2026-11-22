"use strict";
const assert=require("node:assert/strict");
const eq=(x,y)=>assert.equal(x,y);
const p2=n=>1n<<BigInt(n);
const p3=n=>3n**BigInt(n);

// Exact combinatorial count by a surviving ballot DP versus cycle recurrence.
const B=[1n],U=[0n],threshold=[0];
let good=[1n], pascal=[1n];
for(let n=1;n<=256;n++){
  let a=0;
  while(p3(a)<p2(n))a++;
  threshold.push(a);
  let row=Array(n+1).fill(0n), newgood=Array(n+1).fill(0n);
  for(let j=0;j<=n;j++){
    row[j]=(pascal[j]??0n)+(pascal[j-1]??0n);
    if(j>=a)newgood[j]=(good[j]??0n)+(good[j-1]??0n);
  }
  const tail=row.slice(a).reduce((x,y)=>x+y,0n);
  const total=newgood.reduce((x,y)=>x+y,0n);
  U.push(tail);B.push(total);
  let algebra=0n;
  for(let j=1;j<=n;j++)algebra+=U[j]*B[n-j];
  eq(BigInt(n)*B[n],algebra);
  assert(BigInt(n)*total>=row[a]);
  good=newgood;pascal=row;
}

const stat={recurrences:256,periodicResidues:0,modifiedEdges:0,equalityEdges:0,
  ordinaryShiftEdges:0,periodicMasks:[],shellSamples:0,literalShellCounts:[],
  finiteCoefficientDisagreements:0,literalStarts:0,maxModifiedSteps:0,
  largestTrace:0,visits:0,fracStarts:0,fracVisits:0,fracLongest:0,fracMaxFlips:0,fracShells:[]};
const T=(x)=>x%2?(3*x+1)/2:x/2; // Exact within the small safe-integer periodic controls.
for(let k=1;k<=16;k++){
  const n=2**k,half=n/2;
  const c=new Int32Array(n),word=new Int32Array(n),flip=new Uint8Array(n);
  let count=0;
  for(let x=0;x<n;x++){
    let u=x,a=1,w=0,m=n;
    for(let j=1;j<=k;j++){
      const b=u%2;w=2*w+b;
      if(b)a*=3;
      m=Math.min(m,a*2**(k-j));
      u=T(u);
    }
    c[x]=m;word[x]=w;
    if(m===n){eq(x%2,1);flip[x]=1;count++;}
  }
  eq(BigInt(count),B[k]);
  stat.periodicMasks.push(count);stat.periodicResidues+=n;
  const deg=new Uint8Array(n), strictAdj=Array.from({length:n},()=>[]);
  for(let r=0;r<n;r++){
    const sp=T(r)%n,sp2=(sp+half)%n;
    eq(Math.floor(word[sp]/2),word[r]%half);
    eq(Math.floor(word[sp2]/2),word[r]%half);
    assert((word[sp]^word[sp2])===1);
    stat.ordinaryShiftEdges+=2;
    const a=flip[r]||r%2===0?1:3;
    const b=flip[r]?((r+1)/2)%n:sp;
    for(const s of [b,(b+half)%n]){
      assert(a*c[s]<=2*c[r]);stat.modifiedEdges++;
      if(a*c[s]===2*c[r]){
        strictAdj[r].push(s);deg[s]++;stat.equalityEdges++;
      }
    }
  }
  // The equality edges alone must have no directed cycle.
  const queue=[];
  for(let x=0;x<n;x++)if(!deg[x])queue.push(x);
  for(let i=0;i<queue.length;i++)for(const y of strictAdj[queue[i]])if(!--deg[y])queue.push(y);
  eq(queue.length,n);
}
const bigT=x=>x&1n?(3n*x+1n)>>1n:x>>1n;
const cache=new Map();
function W(x){
  if(cache.has(x))return cache.get(x);
  let u=x,m=x,k=x.toString(2).length-1;
  for(let j=0;j<k;j++){u=bigT(u);if(u<m)m=u;}
  cache.set(x,m);return m;
}
for(let k=1;k<=16;k++){
  let n=0,coeff=0;
  for(let x=p2(k);x<p2(k+1);x++){
    const literal=W(x)===x;
    if(literal)n++;
    let t=x,p=1n,possible=true;
    for(let j=1;j<=k;j++){
      if(t&1n)p*=3n;
      t=bigT(t);
      if(p<p2(j)){possible=false;break;}
    }
    if(possible){coeff++;assert(literal);}
    stat.shellSamples++;
  }
  eq(BigInt(coeff),B[k]);
  stat.literalShellCounts.push(n);
  stat.finiteCoefficientDisagreements+=n-coeff;
}
for(let x=1n;x<=32768n;x++){
  stat.literalStarts++;
  let u=x,h=0,flips=0;
  while(u>2n){
    const w=W(u),changed=(u&1n)&&w===u;
    const z=changed?(u+1n)/2n:bigT(u);
    assert(changed?W(z)<w:W(z)<=w);
    if(changed)flips++;
    u=z;h++;assert(h<2000);
    stat.visits++;
  }
  assert(BigInt(flips)<W(x));
  stat.maxModifiedSteps=Math.max(stat.maxModifiedSteps,flips);
  stat.largestTrace=Math.max(stat.largestTrace,h);
}
for(let k=1;k<=16;k++){
  let n=0;
  for(let x=p2(k);x<p2(k+1);x++)if((x&1n)&&4n*W(x)>3n*x)n++;
  assert(B[k]<=BigInt(n)&&BigInt(n)<=B[k+4]);
  stat.fracShells.push(n);
}
for(let x=1n;x<=32768n;x++){
  let v=x,t=0,flips=0,w0=W(x);stat.fracStarts++;
  while(v>2n){
    const w=W(v),changed=(v&1n)&&4n*w>3n*v;
    const z=changed?(v+1n)/2n:bigT(v);
    if(changed){
      assert(9n*W(z)<8n*w&&3n*v<4n*w0&&z<=x);flips++;
    }else assert(W(z)<=w);
    v=z;t++;assert(t<2000);stat.fracVisits++;
  }
  stat.fracLongest=Math.max(stat.fracLongest,t);
  stat.fracMaxFlips=Math.max(stat.fracMaxFlips,flips);
}
console.log(JSON.stringify(stat));
