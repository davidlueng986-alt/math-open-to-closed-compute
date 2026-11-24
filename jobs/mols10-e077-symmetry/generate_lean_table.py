#!/usr/bin/env python3
import json
from pathlib import Path
root=Path(__file__).parent
data=json.loads((root/'orbit_transports.json').read_text())
header='''import Mathlib
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace MOLS10.E077.OrbitTable
structure Transport where
  input : Nat × Nat
  target : Nat × Nat
  perm : List Nat
  deriving DecidableEq
structure Shard where
  p : List Nat
  reps : List (Nat × Nat)
  transports : List Transport

def entry (xs : List Nat) (i : Nat) : Nat := xs[i]?.getD 100

def validPermutation (xs : List Nat) : Bool :=
  xs.length == 10 && (List.range 10).all (fun y =>
    (xs.filter (fun x => x == y)).length == 1)

def allPairs : List (Nat × Nat) :=
  (List.range 10).flatMap (fun a =>
    ((List.range 10).filter (fun b => decide (2 ≤ a ∧ a < b))).map (fun b => (a,b)))

def transportValid (s : Shard) (t : Transport) : Bool :=
  validPermutation t.perm && entry t.perm 0 == 0 &&
  (List.range 10).all (fun x => entry t.perm (entry s.p x) == entry s.p (entry t.perm x)) &&
  s.reps.contains t.target &&
  ((entry t.perm t.input.1 == t.target.1 && entry t.perm t.input.2 == t.target.2) ||
   (entry t.perm t.input.1 == t.target.2 && entry t.perm t.input.2 == t.target.1))

def shardValid (s : Shard) : Bool :=
  validPermutation s.p && entry s.p 0 == 1 &&
  (s.transports.map Transport.input == allPairs) &&
  (s.reps.all (fun ab => allPairs.contains ab)) &&
  s.transports.all (transportValid s)

'''
lines=[header]
for row in data['shards']:
 i=row['shard']
 def pair(p):return '('+str(p[0])+','+str(p[1])+')'
 reps='['+','.join(pair(p) for p in row['representatives'])+']'
 trs=[]
 for t in row['transports']:
  trs.append('⟨'+pair(t['pair'])+','+pair(t['target'])+','+str(t['permutation'])+'⟩')
 lines.append(f'def shard{i} : Shard := ⟨{row["p"]},{reps},[\n'+',\n'.join(trs)+']⟩\n')
 lines.append(f'theorem shard{i}_checked : shardValid shard{i} = true := by decide\n')
 lines.append(f'#print axioms shard{i}_checked\n')
lines.append('def allShards : List Shard := ['+','.join('shard'+str(i) for i in range(12))+']\n')
lines.append('def parityShards : List Shard := [shard1,shard2,shard6,shard8,shard9,shard10]\n')
lines.append('theorem parity_representative_count : ((parityShards.map (fun s => s.reps.length)).sum) = 31 := by decide\n#print axioms parity_representative_count\n')
lines.append('theorem original_pair_count : allPairs.length = 28 := by decide\n')
lines.append('theorem representative_count : ((allShards.map (fun s => s.reps.length)).sum) = 79 := by decide\n')
lines.append('#print axioms original_pair_count\n#print axioms representative_count\nend MOLS10.E077.OrbitTable\n')
(root/'OrbitTable.lean').write_text('\n'.join(lines))
