import PASoundness.PAtoCompactSuccInjectMatrixExtract
import PASoundness.PAtoCompactFreeNames

/-! Free-name bounds needed to eliminate the two extracted successor child
witnesses. These are syntax facts, not successor injectivity or PA axioms. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccInjectFrameFree

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactSuccTermSpareAlpha PASoundness.PAtoCompactSuccInjectMatrixExtract
open PASoundness.PAtoCompactFreeNames

/-- A label below both result names and above the two term-variable supports
is absent from any matrix using those results, independently of the private
allocator bases. -/
theorem matrix_free_middle (t u : Peano.Term) (w z p q r x : Nat)
    (hxw : x < w) (hxz : x < z)
    (ht : ∀ a ∈ t.varFinset, a < x) (hu : ∀ a ∈ u.varFinset, a < x) :
    x ∉ (matrix id t u w z p q r).free := by
  intro h
  simp only [matrix, andF_free, Finset.mem_union] at h
  rcases h with h | h | h
  · have hh := termGraph_free_subset id t w p h
    rcases Finset.mem_union.mp hh with hv | ho
    · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hv
      simp only [id_eq] at he
      have := ht a ha
      omega
    · have := Finset.mem_singleton.mp ho
      omega
  · have hh := termGraph_free_subset id u z q h
    rcases Finset.mem_union.mp hh with hv | ho
    · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hv
      simp only [id_eq] at he
      have := hu a ha
      omega
    · have := Finset.mem_singleton.mp ho
      omega
  · have hh := equivAt_free r w z h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    omega

/-- The spare name occurs in neither the actual successor equality matrix nor
the target equality frame, when it is between source names and b. -/
theorem source_target_free (t u : Peano.Term) (b x : Nat)
    (hxb : x < b)
    (ht : ∀ a ∈ t.varFinset, a < x) (hu : ∀ a ∈ u.varFinset, a < x) :
    x ∉ (sourceMatrix t u b).free ∧ x ∉ (equalityFrame id t u b).free := by
  have hst : ∀ a ∈ (Peano.succ t).varFinset, a < x := by
    intro a ha
    apply ht a
    simpa [Peano.succ, Term.varFinset] using ha
  have hsu : ∀ a ∈ (Peano.succ u).varFinset, a < x := by
    intro a ha
    apply hu a
    simpa [Peano.succ, Term.varFinset] using ha
  constructor
  · exact matrix_free_middle (Peano.succ t) (Peano.succ u) b (b+1) _ _ _ x
      hxb (by omega) hst hsu
  · have hm := matrix_free_middle t u b (b+1) (b+2) (b+2+termCost t)
      (b+2+termCost t+termCost u) x hxb (by omega) ht hu
    intro h
    have h' : x ∈ (matrix id t u b (b+1) (b+2) (b+2+termCost t)
      (b+2+termCost t+termCost u)).free := by
      simp only [equalityFrame, Formula.free, Finset.mem_erase] at h
      exact h.2.2
    exact hm h'

/-- The second spare is absent from the first spare's extracted body when it
lies strictly between that spare and the output name, above all term names. -/
theorem second_spare_not_first_body (t : Peano.Term) (b a c : Nat)
    (hac : a < c) (hcb : c < b) (ht : ∀ x ∈ t.varFinset, x < a) :
    c ∉ (spareBody id t b (b+2) a).free := by
  intro h
  simp only [spareBody, andF_free, Finset.mem_union] at h
  rcases h with hg | hs
  · have hh := termGraph_free_subset id t a (b+2+64) hg
    rcases Finset.mem_union.mp hh with hv | ho
    · obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hv
      simp only [id_eq] at he
      have := ht x hx
      omega
    · have := Finset.mem_singleton.mp ho
      omega
  · have hh := succAt_free (b+2) a b hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    omega

end PASoundness.PAtoCompactSuccInjectFrameFree

#print axioms PASoundness.PAtoCompactSuccInjectFrameFree.matrix_free_middle
#print axioms PASoundness.PAtoCompactSuccInjectFrameFree.source_target_free
#print axioms PASoundness.PAtoCompactSuccInjectFrameFree.second_spare_not_first_body
