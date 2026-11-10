import PASoundness.PAtoCompactTermZeroGuarded
import PASoundness.PAtoCompactFreeNames
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.PAtoCompactGuardBaseTransport

/-! Construct the exact generated multiplication-node graph from the two child graph
existence proofs and an explicit candidate-multiplication existence family. All
freshness obligations are discharged from free-name bounds. The multiplication
family remains proof data; no general arithmetic totality is assumed. -/
namespace PASoundness.PAtoCompactMultiplicationGraphFromChildren

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermZeroGuarded
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactSuccTermTotality

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Multiplication output existence at arbitrary bounded labels. The operand labels
may coincide; the existential output label must be fresh for both. -/
structure MultiplicationExistence where
  next : ∀ (b x y out : Nat), x < b+2 → y < b+2 → out < b+2 → x ≠ out → y ≠ out →
    KDerivation (imp (domainAt b x).encode
      (imp (domainAt b y).encode
        (existsCode out (andF (domainAt b out) (mulAt b x y out)).encode)))

/-- Combine two actual child graph proofs with candidate multiplication existence.
No restriction is placed on the children's term constructors. -/
def mul_total_from_children {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (b out : Nat) (g : Formula)
    (hout : out < b) (hg : ∀ z ∈ g.free, z < out)
    (ht : ∀ a ∈ t.varFinset, v a < out) (hu : ∀ a ∈ u.varFinset, v a < out)
    (next : MultiplicationExistence)
    (child1 : KDerivation (imp g.encode
      (existsCode b (termGraph v t b (b+64)).encode)))
    (child2 : KDerivation (imp g.encode
      (existsCode (b+1) (termGraph v u (b+1) (b+64+termCost t)).encode))) :
    KDerivation (imp g.encode (existsCode out
      (termGraph v (binaryTerm false t u) out b).encode)) := by
  let T := termGraph v t b (b+64)
  let U := termGraph v u (b+1) (b+64+termCost t)
  let E := Formula.ex out (termGraph v (binaryTerm false t u) out b)
  have hG (k : Nat) (hk : out ≤ k) : k ∉ g.free := by
    intro hm
    have hh := hg k hm
    omega
  have hT (k : Nat) (hk : out ≤ k) (hkb : k ≠ b) : k ∉ T.free := by
    intro hm
    have hh := termGraph_free_subset v t b (b+64) hm
    rcases Finset.mem_union.mp hh with hh | hh
    · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hh
      have hl := ht a ha
      omega
    · exact hkb (Finset.mem_singleton.mp hh)
  have hU (k : Nat) (hk : out ≤ k) (hkb : k ≠ b+1) : k ∉ U.free := by
    intro hm
    have hh := termGraph_free_subset v u (b+1) (b+64+termCost t) hm
    rcases Finset.mem_union.mp hh with hh | hh
    · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hh
      have hl := hu a ha
      omega
    · exact hkb (Finset.mem_singleton.mp hh)
  have hE (k : Nat) (hk : out ≤ k) : k ∉ E.free := by
    intro hm
    have he : k ≠ out ∧ k ∈ (termGraph v (binaryTerm false t u) out b).free := by
      simpa [E, Formula.free] using hm
    have hh := termGraph_free_subset v (binaryTerm false t u) out b he.2
    rcases Finset.mem_union.mp hh with hh | hh
    · obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hh
      have ha' : a ∈ t.varFinset ∨ a ∈ u.varFinset := by
        simpa [binaryTerm, Term.varFinset] using ha
      rcases ha' with ha' | ha'
      · have hl := ht a ha'; omega
      · have hl := hu a ha'; omega
    · exact he.1 (Finset.mem_singleton.mp hh)
  have op : KDerivation (imp T.encode (imp U.encode
      (existsCode out (andF (domainAt b out) (binaryRel false b b (b+1) out)).encode))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [U.encode, T.encode]
    have hT' : Context Γ T.encode := .hypothesis (by simp [Γ])
    have hU' : Context Γ U.encode := .hypothesis (by simp [Γ])
    have hd0 : Context Γ (domainAt (b+64) b).encode := .mp hT' (.closed (termGraph_domain v t b (b+64)))
    have hd1 : Context Γ (domainAt (b+64+termCost t) (b+1)).encode :=
      .mp hU' (.closed (termGraph_domain v u (b+1) (b+64+termCost t)))
    have hx : Context Γ (domainAt b b).encode := .mp hd0
      (.closed (PAtoCompactGuardBaseTransport.domainAt_transport (b+64) b b (by omega) (by omega)))
    have hy : Context Γ (domainAt b (b+1)).encode := .mp hd1
      (.closed (PAtoCompactGuardBaseTransport.domainAt_transport (b+64+termCost t) b (b+1)
        (by omega) (by omega)))
    have hres := next.next b b (b+1) out (by omega) (by omega) (by omega) (by omega) (by omega)
    simpa [binaryRel] using (Context.mp hy (Context.mp hx (.closed hres)))
  have result := binary_total_from_children v false t u b out g hout
    child1 child2 op
    (free_vacuity b g (hG b (by omega)))
    (free_vacuity (b+1) g (hG (b+1) (by omega)))
    (free_vacuity out g (hG out (by omega)))
    (free_vacuity (b+1) T (hT (b+1) (by omega) (by omega)))
    (free_vacuity out T (hT out (by omega) (by omega)))
    (free_vacuity out U (hU out (by omega) (by omega)))
    (by simpa [E, Formula.encode] using free_vacuity b E (hE b (by omega)))
    (by simpa [E, Formula.encode] using free_vacuity (b+1) E (hE (b+1) (by omega)))
    (by simpa [E, Formula.encode] using free_vacuity out E (hE out (by omega)))
  exact result

end PASoundness.PAtoCompactMultiplicationGraphFromChildren
#print axioms PASoundness.PAtoCompactMultiplicationGraphFromChildren.mul_total_from_children
