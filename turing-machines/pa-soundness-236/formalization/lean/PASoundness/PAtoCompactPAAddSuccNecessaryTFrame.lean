import PASoundness.PAtoCompactScopedEqualityReplace
import PASoundness.PAtoCompactFreeVacuity

/-! A finite K equality-frame projection of the left graph witness.
It does not assert that any equality frame or term graph exists. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPAAddSuccNecessaryTFrame
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactFreeVacuity

/-- Extract the left graph witness from the actual equality frame. The bound
ensures that its free variables avoid the right witness label. -/
def equality_frame_left_graph {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (b : Nat)
    (ht : ∀ a ∈ t.varFinset, v a < b) :
    KDerivation (imp (equalityFrame v t u b).encode
      (existsCode b (termGraph v t b (b+2)).encode)) := by
  let L := termGraph v t b (b+2)
  let R := termGraph v u (b+1) (b+2+termCost t)
  let E := equivAt (b+2+termCost t+termCost u) b (b+1)
  let M := andF L (andF R E)
  have hp : KDerivation (imp M.encode L.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [M.encode]
    have hm : Context Γ (both L.encode (both R.encode E.encode)) := by
      have h := Context.head [] M.encode
      simpa [Γ, M, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using h
    exact Context.conjunctionLeft hm
  have hfree : b+1 ∉ L.free := by
    intro hm
    have hs := termGraph_free_subset v t b (b+2) hm
    rcases Finset.mem_union.mp hs with h | h
    · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp h
      have hl := ht a ha
      omega
    · have he := Finset.mem_singleton.mp h
      omega
  have hinner : KDerivation (imp (existsCode (b+1) M.encode) L.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.existsElim (free_vacuity (b+1) L hfree)
      (.closed (.generalize (b+1) hp)) (Context.head [] _)
  have h := existsCongr b hinner
  simpa [equalityFrame, L, R, E, M, Formula.encode, existsCode] using h

theorem equality_frame_left_graph_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (b : Nat)
    (ht : ∀ a ∈ t.varFinset, v a < b) :
    theoremCode (certificate (equality_frame_left_graph v t u b ht)) =
      imp (equalityFrame v t u b).encode
        (existsCode b (termGraph v t b (b+2)).encode) := certificate_correct _
end PASoundness.PAtoCompactPAAddSuccNecessaryTFrame
#print axioms PASoundness.PAtoCompactPAAddSuccNecessaryTFrame.equality_frame_left_graph
#print axioms PASoundness.PAtoCompactPAAddSuccNecessaryTFrame.equality_frame_left_graph_certificate
