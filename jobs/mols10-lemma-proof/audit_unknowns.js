#!/usr/bin/env node
// E074: audit the actual E073 unresolved stacks using duplicate-XOR rigidity.
// Usage: node audit_unknowns.js coarse_lift_summary.json
const fs=require("node:fs");
const assert=require("node:assert/strict");
const crypto=require("node:crypto");
const source=JSON.parse(fs.readFileSync(process.argv[2],"utf8"));
function basis(rows){let b=Array(20).fill(0),rank=0;for(let x of rows){while(x){let k=31-Math.clz32(x);if(b[k])x^=b[k];else{b[k]=x;rank++;break}}}return {b,rank}}
function dconstant(rows){let {b}=basis(rows);for(let t=1;t<5;t++){let x=1|(1<<t);while(x){let k=31-Math.clz32(x);if(b[k])x^=b[k];else break}if(x)return false;}return true}
function feasible(edges,mask){let parent=Array.from({length:15},(_,i)=>i), parity=Array(15).fill(0);function find(x){if(parent[x]===x)return [x,0];let [p,v]=find(parent[x]);parity[x]^=v;parent[x]=p;return[p,parity[x]]}function add(x,y,v){let [a,c]=find(x),[b,d]=find(y);if(a===b)return (c^d)===v;parent[a]=b;parity[a]=c^d^v;return true}for(let [c,d,e] of edges){let zero=(mask>>c)&1;if(!add(5+d,10+e,zero^1))return false;if(zero&&!add(c,5+d,0))return false;}return true}
function audit(t){
  assert.equal(t.length,500);assert(/^[0-4]+$/.test(t));
  const layers=Array.from({length:4},(_,l)=>Array.from({length:25},(_,q)=>t.slice(125*l+5*q,125*l+5*q+5).split("").map(Number)));
  for(const L of layers)for(let i=0;i<5;i++)for(let j=i+1;j<5;j++)assert.equal(new Set(L.map(r=>5*r[i]+r[j])).size,25);
  let ls=layers.map(L=>L.map(r=>r.join("")).sort().join(",")),groups=[];
  for(let l=0;l<4;l++){let k=groups.findIndex(g=>ls[g[0]]===ls[l]);if(k<0)groups.push([l]);else groups[k].push(l)}
  groups.sort((a,b)=>b.length-a.length);
  if(groups.length===4)return {status:"OPEN",reason:"four distinct layers"};
  assert(groups.length===2||groups.length===3);
  let buckets=Array.from({length:25},()=>Array.from({length:20},()=>[]));
  for(let g=0;g<groups.length;g++)for(const a of layers[groups[g][0]])for(let i=0;i<5;i++)for(let j=0;j<5;j++)if(i!==j)buckets[5*i+a[i]][5*(j<i?j:j-1)+a[j]][g]=a[i===0?1:0];
  for(const f of buckets)for(const e of f)assert.equal(e.filter(Number.isInteger).length,groups.length);
  let masks=buckets.map(f=>f.map(e=>e.reduce((m,t,g)=>m|(1<<(5*g+t)),0)));
  let rigid=0;
  if(groups.length===2){assert(groups.every(g=>g.length===2));for(let i=0;i<5;i++)if(masks.slice(5*i,5*i+5).every(m=>basis(m).rank===9))rigid++;return {status:rigid>=4?"UNSAT_LEMMA":"OPEN",reason:"two repeated pairs: constant XOR",rigid}}
  assert.deepEqual(groups.map(g=>g.length),[2,1,1]);
  for(let i=0;i<5;i++)if(masks.slice(5*i,5*i+5).every(dconstant))rigid++;
  if(rigid>=4)return {status:"UNSAT_LEMMA",reason:"linear projection forces duplicate XOR fibre-constant",rigid};
  let exact=0;
  for(let i=0;i<5;i++)if(buckets.slice(5*i,5*i+5).every(e=>{for(let m=1;m<31;m++)if(feasible(e,m))return false;return true}))exact++;
  return {status:exact>=4?"UNSAT_LEMMA":"OPEN",reason:"exact balance signed-graph projection",rigid,exact};
}
let cases=source.unknown_stacks.map(t=>({sha256:crypto.createHash("sha256").update(t).digest("hex"),...audit(t)}));
let summary={input_count:cases.length,excluded:cases.filter(x=>x.status==="UNSAT_LEMMA").length,remaining:cases.filter(x=>x.status==="OPEN").length,reasons:{}};
for(const c of cases)summary.reasons[c.reason]=(summary.reasons[c.reason]||0)+1;
console.log(JSON.stringify({summary,cases},null,2));
