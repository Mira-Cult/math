import PASoundness.PAtoCompactPAAddZeroSharedGraph
import PASoundness.PAtoCompactPAAddZeroRelation
import PASoundness.PAtoCompactZeroTermTotality
import PASoundness.PAtoCompactZeroBaseTransport
import PASoundness.PAtoCompactSuccTermTotality
import PASoundness.PAtoCompactFreeVacuity

/-! Construct an addition-by-zero term graph from an existing child graph,
using the same output value. This is finite K proof data and does not construct
an arbitrary child's graph existence. -/
namespace PASoundness.PAtoCompactPAAddZeroGraphFromChild
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermZeroGuarded
open PASoundness.PAtoCompactPAAddZeroSharedGraph PASoundness.PAtoCompactPAAddZeroRelation
open PASoundness.PAtoCompactTermGraphBinderRange PASoundness.PAtoCompactSuccTermTotality
open PASoundness.PAtoCompactGuardBaseTransport PASoundness.PAtoCompactZeroBaseTransport
open PASoundness.PAtoCompactZeroTermTotality PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactFreeNames
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Existing child graph implies the graph of `t + 0` at exactly the same
output. The labels are syntactic names; no semantic distinctness is assumed. -/
noncomputable def add_zero_from_child {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) (b q : Nat) (hq : q < b)
    (hv : ∀ a ∈ t.varFinset, v a < b) :
    KDerivation (imp (termGraph v t q (b+64)).encode
      (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) q b).encode) := by
  let z : Peano.language.Term α := .func .zero Fin.elim0
  let G := termGraph v t q (b+64)
  let Z := termGraph v z (b+1) (b+64+termCost t)
  let T := termGraph v (binaryTerm true t z) q b
  have hg : b+1 ∉ G.free := by
    intro h
    have hh := termGraph_free_subset v t q (b+64) h
    rcases Finset.mem_union.mp hh with hh | hh
    · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hh
      have hl := hv a ha
      omega
    · have hh := Finset.mem_singleton.mp hh
      omega
  have ht : b+1 ∉ T.free := by
    intro h
    have hh := termGraph_free_subset v (binaryTerm true t z) q b h
    rcases Finset.mem_union.mp hh with hh | hh
    · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hh
      have ha' : a ∈ t.varFinset := by simpa [binaryTerm, z, Term.varFinset] using ha
      have hl := hv a ha'
      omega
    · have hh := Finset.mem_singleton.mp hh
      omega
  have hzero : KDerivation (existsCode (b+1) Z.encode) := by
    simpa [Z, z] using zero_term_total v (b+64+termCost t) (b+1) (by omega)
  have hvG := free_vacuity (b+1) G hg
  have hvT := free_vacuity (b+1) T ht
  have hIntro := shared_graph_intro v t b q hq hv
  have hRel := right_zero_same_output b q (b+1) (by omega) (by omega)
  have hD := compose (termGraph_domain v t q (b+64))
    (domainAt_transport (b+64) b q (by omega) (by omega))
  have hZ := zeroAt_base_forward (b+64+termCost t) b (b+1) (by omega) (by omega)
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [G.encode]
  have hex : Context Γ (existsCode (b+1) Z.encode) := .closed hzero
  apply Context.existsElim hvT _ hex
  apply generalizeOne (b+1) hvG
  apply Context.deduction
  let Δ := [Z.encode, G.encode]
  have hz : Context Δ Z.encode := .head _ _
  have hg' : Context Δ G.encode := .hypothesis (by simp [Δ])
  have hzboth : Context Δ (both (domainAt (b+64+termCost t) (b+1)).encode
      (zeroAt (b+64+termCost t) (b+1)).encode) := by
    simpa [Z, z, termGraph, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using hz
  have hz' : Context Δ (zeroAt b (b+1)).encode := .mp (Context.conjunctionRight hzboth) (.closed hZ)
  have hd : Context Δ (domainAt b q).encode := .mp hg' (.closed hD)
  have hr : Context Δ (addAt b q (b+1) q).encode := .mp hz' (.mp hd (.closed hRel))
  exact .mp hr (.mp hz (.mp hg' (.mp hd (.closed hIntro))))

#print axioms add_zero_from_child
end PASoundness.PAtoCompactPAAddZeroGraphFromChild
