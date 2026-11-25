import Leaves
import TriangleCut

namespace E64Closed
open SimpleGraph Erdos64Closure E64Core E64Leaves
universe u

theorem exclude_ct_core : Exclude.{u} (Leaf.ct .core) := by
  intro V G _ _ hm hleaf
  obtain ⟨hC,_,htri,_,hcut⟩ := hleaf
  have htri_copy := htri
  obtain ⟨a,_,_,_,_,_⟩ := htri_copy
  exact hcut (E64Triangle.near_subcubic_triangle_cut G a
    (fun v => (hC v).le) (fun v _ => hC v) htri hm.2.1)

theorem exclude_st_core : Exclude.{u} (Leaf.st .core) := by
  intro V G _ _ hm hleaf
  obtain ⟨⟨w,hw,hdeg⟩,_,htri,_,hcut⟩ := hleaf
  have hmax (v : V) : G.degree v ≤ 3 := by
    by_cases h : v=w
    · subst v; omega
    · exact (hdeg v h).le
  exact hcut (E64Triangle.near_subcubic_triangle_cut G w hmax hdeg htri hm.2.1)

#print axioms exclude_ct_core
#print axioms exclude_st_core
end E64Closed

