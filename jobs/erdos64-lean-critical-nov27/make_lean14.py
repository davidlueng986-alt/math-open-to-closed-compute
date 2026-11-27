import json,itertools
from pathlib import Path
here=Path(__file__).resolve().parent
w=json.loads((here/'witness14.json').read_text())
n=w['order'];edges=w['edges'];paths=w['pair_exit_paths'];cycles=w['cycles']
a=[set()for _ in range(n)]
for u,v in edges:a[u].add(v);a[v].add(u)
N=len(paths);C=len(cycles)
def walk(p):
 out='Walk.nil'
 for u,v in reversed(list(zip(p,p[1:]))):out=f'(Walk.cons (show G.Adj {u} {v} from by decide) {out})'
 return out
s='''import Shadow

/-!
Exact fourteen-vertex obstruction to using the known dyadic-path consequences
alone. The graph is triangle-free, subcubic, and NOT Near. All pairs have
power-length paths; distant pairs have two exits; every induced P3 is on
both a 9-cycle and a 6- or 10-cycle. Nevertheless there is no power cycle.
This is not an original Erdős–Gyárfás counterexample or a terminal exclusion.
All finite facts use ordinary kernel reduction, with actual SimpleGraph.Walk
witnesses and the original unbounded HasPower predicate.
-/
namespace E64AllPairsObstruction
open SimpleGraph Erdos64Closure
open scoped Sym2
set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev V := Fin 14

def edgeList : List (V × V) :=
  '''+str([tuple(e) for e in edges])+'''

def Adj (u v : V) : Prop := (u,v) ∈ edgeList ∨ (v,u) ∈ edgeList
instance adjDecidable : DecidableRel Adj := fun u v =>
  inferInstanceAs (Decidable ((u,v) ∈ edgeList ∨ (v,u) ∈ edgeList))

def G : SimpleGraph V where
  Adj := Adj
  symm := ⟨by intro u v h; exact h.elim Or.inr Or.inl⟩
  loopless := ⟨by intro u; fin_cases u <;> decide⟩
instance graphAdjDecidable : DecidableRel G.Adj := adjDecidable

def DyadicPath {W : Type*} (H : SimpleGraph W) (u v : W) : Prop :=
  ∃ (k : ℕ) (p : H.Walk u v), 2 ≤ k ∧ p.IsPath ∧ p.length = 2^k

structure PathCert where
  start : V
  stop : V
  exit : V
  exponent : ℕ
  walk : G.Walk start stop
  exponent_ge : 2 ≤ exponent
  path : walk.IsPath
  len : walk.length = 2^exponent
  first : walk.snd = exit

'''
for i,d in enumerate(paths):
 p=d['path'];u=d['source'];v=d['target'];e=d['exit'];k={4:2,8:3}[len(p)-1]
 s+=f'''def pc{i} : PathCert := by
  refine ⟨{u},{v},{e},{k},{walk(p)},by decide,?_,rfl,rfl⟩
  apply Walk.IsPath.mk'
  decide

'''
s+='def pathData : Array PathCert := #[\n  '+', '.join('pc'+str(i)for i in range(N))+'\n]\n'
s+=f'''def pathAt (i : Fin {N}) : PathCert :=
  pathData[i.val]'(by simpa [pathData] using i.isLt)

'''
by_pair={}
for i,d in enumerate(paths):by_pair.setdefault((d['source'],d['target']),[]).append(i)
for name,choice in [('firstIndex',0),('secondIndex',1)]:
 rows=[]
 for u in range(n):
  rows.append('#['+', '.join(str(by_pair.get((u,v),[0])[min(choice,len(by_pair.get((u,v),[0]))-1)])for v in range(n))+']')
 s+=f'''def {name} (u v : V) : Fin {N} :=
  ((#[
    '''+',\n    '.join(rows)+f'''
  ] : Array (Array (Fin {N})))[u.val]!)[v.val]!

'''
s+='''theorem first_checked : ∀ u v : V, u ≠ v →
    (pathAt (firstIndex u v)).start = u ∧ (pathAt (firstIndex u v)).stop = v := by
  decide

#print axioms first_checked

theorem all_pairs_dyadic : ∀ u v : V, u ≠ v → DyadicPath G u v := by
  intro u v h
  obtain ⟨hs,ht⟩ := first_checked u v h
  have hp : DyadicPath G (pathAt (firstIndex u v)).start (pathAt (firstIndex u v)).stop :=
    ⟨_,_,(pathAt (firstIndex u v)).exponent_ge,
      (pathAt (firstIndex u v)).path,(pathAt (firstIndex u v)).len⟩
  simpa only [hs,ht] using hp

def TwoExitProperty : Prop :=
  ∀ u v : V, u ≠ v → ¬G.Adj u v → (∀ z : V, ¬(G.Adj u z ∧ G.Adj z v)) →
    ∃ (k l : ℕ) (p q : G.Walk u v),
      2 ≤ k ∧ 2 ≤ l ∧ p.IsPath ∧ q.IsPath ∧
      p.length = 2^k ∧ q.length = 2^l ∧ p.snd ≠ q.snd

theorem exits_checked : ∀ u v : V, u ≠ v → ¬G.Adj u v →
    (∀ z : V, ¬(G.Adj u z ∧ G.Adj z v)) →
    (pathAt (secondIndex u v)).start = u ∧
    (pathAt (secondIndex u v)).stop = v ∧
    (pathAt (firstIndex u v)).exit ≠ (pathAt (secondIndex u v)).exit := by decide

#print axioms exits_checked

theorem two_path_certs (A B : PathCert) (u v : V)
    (hs : A.start = u) (ht : A.stop = v)
    (hs' : B.start = u) (ht' : B.stop = v) (he : A.exit ≠ B.exit) :
    ∃ (k l : ℕ) (p q : G.Walk u v),
      2 ≤ k ∧ 2 ≤ l ∧ p.IsPath ∧ q.IsPath ∧
      p.length = 2^k ∧ q.length = 2^l ∧ p.snd ≠ q.snd := by
  rcases A with ⟨s,t,e,k,p,hk,hp,hlen,hfirst⟩
  rcases B with ⟨s',t',e',l,q,hl,hq,hqlen,hqfirst⟩
  change s = u at hs
  change t = v at ht
  change s' = u at hs'
  change t' = v at ht'
  change e ≠ e' at he
  subst u
  subst v
  subst s'
  subst t'
  refine ⟨k,l,p,q,hk,hl,hp,hq,hlen,hqlen,?_⟩
  simpa only [hfirst,hqfirst] using he

theorem two_distinct_exits : TwoExitProperty := by
  intro u v hne hnadj hcommon
  obtain ⟨hs,ht⟩ := first_checked u v hne
  obtain ⟨hs',ht',he⟩ := exits_checked u v hne hnadj hcommon
  exact two_path_certs (pathAt (firstIndex u v)) (pathAt (secondIndex u v))
    u v hs ht hs' ht' he

structure CycleCert where
  base : V
  length : ℕ
  walk : G.Walk base base
  cycle : walk.IsCycle
  len : walk.length = length

'''
for i,c in enumerate(cycles):
 p=c+[c[0]]
 s+=f'''def cc{i} : CycleCert := by
  refine ⟨{c[0]},{len(c)},{walk(p)},?_,rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    decide
  · decide

'''
s+='def cycleData : Array CycleCert := #[\n  '+', '.join('cc'+str(i)for i in range(C))+'\n]\n'
s+=f'''def cycleAt (i : Fin {C}) : CycleCert :=
  cycleData[i.val]'(by simpa [cycleData] using i.isLt)

'''
for name,lengths in [('fermatIndex',{9}),('plusTwoIndex',{6,10})]:
 tab={}
 for x in range(n):
  for aa,bb in itertools.combinations(a[x],2):
   for i,c in enumerate(cycles):
    if len(c)not in lengths or x not in c:continue
    j=c.index(x)
    if {c[j-1],c[(j+1)%len(c)]}=={aa,bb}:
     tab[x,aa,bb]=i;tab[x,bb,aa]=i;break
   assert(x,aa,bb)in tab
 s+=f'''def {name} (x a b : V) : Fin {C} :=
  match x.val,a.val,b.val with
'''
 for (x,aa,bb),i in sorted(tab.items()):s+=f'  | {x},{aa},{bb} => {i}\n'
 s+='  | _,_,_ => 0\n\n'
s+='''theorem fermat_checked : ∀ x a b : V, a ≠ b → G.Adj x a → G.Adj x b →
    (cycleAt (fermatIndex x a b)).length = 9 ∧
    s(x,a) ∈ (cycleAt (fermatIndex x a b)).walk.edges ∧
    s(x,b) ∈ (cycleAt (fermatIndex x a b)).walk.edges := by decide

#print axioms fermat_checked

theorem plus_two_checked : ∀ x a b : V, a ≠ b → G.Adj x a → G.Adj x b →
    ((cycleAt (plusTwoIndex x a b)).length = 6 ∨
      (cycleAt (plusTwoIndex x a b)).length = 10) ∧
    s(x,a) ∈ (cycleAt (plusTwoIndex x a b)).walk.edges ∧
    s(x,b) ∈ (cycleAt (plusTwoIndex x a b)).walk.edges := by decide

#print axioms plus_two_checked

def P3FermatProperty : Prop :=
  ∀ x a b : V, a ≠ b → G.Adj x a → G.Adj x b →
    ∃ (r : V) (c : G.Walk r r), c.IsCycle ∧ c.length = 9 ∧
      s(x,a) ∈ c.edges ∧ s(x,b) ∈ c.edges

def P3PlusTwoProperty : Prop :=
  ∀ x a b : V, a ≠ b → G.Adj x a → G.Adj x b →
    ∃ (r : V) (c : G.Walk r r), c.IsCycle ∧ (c.length = 6 ∨ c.length = 10) ∧
      s(x,a) ∈ c.edges ∧ s(x,b) ∈ c.edges

theorem p3_fermat : P3FermatProperty := by
  intro x a b hne hxa hxb
  obtain ⟨hlen,ha,hb⟩ := fermat_checked x a b hne hxa hxb
  refine ⟨_,(cycleAt (fermatIndex x a b)).walk,
    (cycleAt (fermatIndex x a b)).cycle,?_,ha,hb⟩
  exact (cycleAt (fermatIndex x a b)).len.trans hlen

theorem p3_plus_two : P3PlusTwoProperty := by
  intro x a b hne hxa hxb
  obtain ⟨hlen,ha,hb⟩ := plus_two_checked x a b hne hxa hxb
  refine ⟨_,(cycleAt (plusTwoIndex x a b)).walk,
    (cycleAt (plusTwoIndex x a b)).cycle,?_,ha,hb⟩
  rcases hlen with hlen | hlen
  · exact Or.inl ((cycleAt (plusTwoIndex x a b)).len.trans hlen)
  · exact Or.inr ((cycleAt (plusTwoIndex x a b)).len.trans hlen)

def neighbors (v : V) : List V :=
  match v.val with
  | 0 => [3, 6, 11]
  | 1 => [4, 7, 10]
  | 2 => [4, 11, 13]
  | 3 => [0, 7, 12]
  | 4 => [1, 2]
  | 5 => [10, 12]
  | 6 => [0, 9, 10]
  | 7 => [1, 3, 8]
  | 8 => [7, 13]
  | 9 => [6, 13]
  | 10 => [1, 5, 6]
  | 11 => [0, 2]
  | 12 => [3, 5]
  | _ => [2, 8, 9]

theorem neighbors_correct : ∀ u v : V, v ∈ neighbors u ↔ G.Adj u v := by decide

def simpleReach : ℕ → V → V → List V → Bool
  | 0, u, v, seen => decide (u = v ∧ u ∉ seen)
  | n+1, u, v, seen =>
      if u ∈ seen then false
      else (neighbors u).any fun w => simpleReach n w v (u::seen)

/-- Every genuine simple walk avoiding the already-used vertices is
accepted by the explicit adjacency-list search. -/
theorem simpleReach_of_path {u v : V} (p : G.Walk u v) :
    p.IsPath → ∀ (seen : List V), (∀ x ∈ p.support, x ∉ seen) →
      simpleReach p.length u v seen = true := by
  induction p with
  | nil =>
    intro _ seen havoid
    have hnot : u ∉ seen := havoid u (by simp)
    simp [simpleReach,hnot]
  | @cons a b c hab q ih =>
    intro hp seen havoid
    have hanot : a ∉ seen := havoid a (by simp)
    change (if a ∈ seen then false else
      (neighbors a).any fun w => simpleReach q.length w c (a::seen)) = true
    rw [if_neg hanot]
    apply List.any_eq_true.mpr
    refine ⟨b, (neighbors_correct a b).mpr hab, ?_⟩
    apply ih (Walk.IsPath.of_cons hp) (a::seen)
    intro x hx
    simp only [List.mem_cons, not_or]
    constructor
    · intro hxa
      subst x
      exact ((Walk.cons_isPath_iff hab q).mp hp).2 hx
    · exact havoid x (by simp [hx])

def cycleSearch (n : ℕ) (u : V) : Bool :=
  (neighbors u).any fun v => simpleReach (n-1) v u []

theorem no_cycle_of_search (n : ℕ) (hcheck : ∀ v : V, cycleSearch n v = false)
    (v : V) (p : G.Walk v v) (hlen : p.length = n) : ¬p.IsCycle := by
  intro hc
  cases p with
  | nil => exact hc.ne_nil rfl
  | cons hab q =>
    have hqpath : q.IsPath := Walk.IsPath.mk' (by simpa using hc.support_nodup)
    have hq := simpleReach_of_path q hqpath [] (by simp)
    have hqn : q.length = n-1 := by simp only [Walk.length_cons] at hlen; omega
    rw [hqn] at hq
    have hcsearch : cycleSearch n v = true := by
      unfold cycleSearch
      apply List.any_eq_true.mpr
      exact ⟨_, (neighbors_correct _ _).mpr hab, hq⟩
    have := hcheck v
    rw [hcsearch] at this
    contradiction

theorem no_four : ∀ (v : V) (p : G.Walk v v), p.length = 4 → ¬p.IsCycle :=
  no_cycle_of_search 4 (by decide)

#print axioms no_four

theorem no_eight : ∀ (v : V) (p : G.Walk v v), p.length = 8 → ¬p.IsCycle :=
  no_cycle_of_search 8 (by decide)

#print axioms no_eight

/-- Exact original power predicate: the graph order bounds all simple
cycle lengths, so there are no unexamined larger exponents. -/
theorem no_power : ¬HasPower G := by
  rintro ⟨k,v,p,hk,hc,hlen⟩
  have hbound : p.length ≤ 14 := by simpa using hc.length_le_natCard
  have hklt : k < 4 := by
    by_contra h
    have hge : 4 ≤ k := by omega
    have hp : (2 : ℕ)^4 ≤ 2^k := Nat.pow_le_pow_right (by omega) hge
    norm_num at hp
    omega
  have hcases : k = 2 ∨ k = 3 := by omega
  rcases hcases with h | h
  · subst k
    exact no_four v p (by simpa using hlen) hc
  · subst k
    exact no_eight v p (by simpa using hlen) hc

theorem triangle_free : ¬∃ a b c : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a := by decide

theorem degrees : ∀ v : V, 2 ≤ G.degree v ∧ G.degree v ≤ 3 := by decide

theorem not_near : ¬Near G := by
  unfold Near
  decide

/-- The combined, unconditional counterexample to the proposed path-only
closure implication, including every tested structural path consequence. -/
theorem counterexample :
    2 ≤ Fintype.card V ∧
    (∀ u v : V, u ≠ v → DyadicPath G u v) ∧
    TwoExitProperty ∧ P3FermatProperty ∧ P3PlusTwoProperty ∧
    (∀ v : V, 2 ≤ G.degree v ∧ G.degree v ≤ 3) ∧
    (¬∃ a b c : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a) ∧
    ¬HasPower G ∧ ¬Near G := by
  exact ⟨by decide,all_pairs_dyadic,two_distinct_exits,p3_fermat,p3_plus_two,
    degrees,triangle_free,no_power,not_near⟩

#print axioms all_pairs_dyadic
#print axioms two_distinct_exits
#print axioms p3_fermat
#print axioms p3_plus_two
#print axioms no_four
#print axioms no_eight
#print axioms no_power
#print axioms counterexample
end E64AllPairsObstruction
'''
(here/'AllPairsObstruction.lean').write_text(s)
print('wrote',len(s),'bytes;',N,'path witnesses;',C,'cycle witnesses')
