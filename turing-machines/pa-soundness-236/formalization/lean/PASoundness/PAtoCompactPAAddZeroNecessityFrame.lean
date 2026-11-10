import PASoundness.PAtoCompactScopedEqualityReplace
import PASoundness.PAtoCompactFreeVacuity

/-! A K proof of an equality frame contains a witness for its right-hand term.
This is a proof-data projection; no semantic soundness is used. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PASoundness.PAtoCompactPAAddZeroNecessityFrame

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactFreeVacuity

/-- Project the right term graph from the actual equality frame. Source names
of that term must be below the frame allocator so the first witness is vacuous
in the target. The source map need not be injective. -/
def equality_frame_right_graph {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (b : Nat)
    (hu : ∀ a ∈ u.varFinset, v a < b) :
    KDerivation (imp (equalityFrame v t u b).encode
      (existsCode (b+1) (termGraph v u (b+1) (b+2+termCost t)).encode)) := by
  let L := termGraph v t b (b+2)
  let R := termGraph v u (b+1) (b+2+termCost t)
  let E := equivAt (b+2+termCost t+termCost u) b (b+1)
  let M := andF L (andF R E)
  have hp : KDerivation (imp M.encode R.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [M.encode]
    have hm : Context Γ (both L.encode (both R.encode E.encode)) := by
      have h := Context.head [] M.encode
      simpa [Γ, M, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using h
    exact Context.conjunctionLeft (Context.conjunctionRight hm)
  have hi := existsCongr (b+1) hp
  have hfreeR : b ∉ R.free := by
    intro hb
    have hs := termGraph_free_subset v u (b+1) (b+2+termCost t) hb
    rcases Finset.mem_union.mp hs with h | h
    · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp h
      have hlt := hu a ha
      omega
    · have he := Finset.mem_singleton.mp h
      omega
  have hfree : b ∉ (Formula.ex (b+1) R).free := by
    simpa [Formula.free] using hfreeR
  apply Context.closeEmpty
  apply Context.deduction
  exact Context.existsElim (free_vacuity b (Formula.ex (b+1) R) hfree)
    (.closed (.generalize b hi)) (by
      have h := Context.head [] (equalityFrame v t u b).encode
      simpa [equalityFrame, L, R, E, M, Formula.encode, existsCode] using h)

theorem equality_frame_right_graph_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (b : Nat)
    (hu : ∀ a ∈ u.varFinset, v a < b) :
    theoremCode (certificate (equality_frame_right_graph v t u b hu)) =
      imp (equalityFrame v t u b).encode
        (existsCode (b+1) (termGraph v u (b+1) (b+2+termCost t)).encode) :=
  certificate_correct _

end PASoundness.PAtoCompactPAAddZeroNecessityFrame

#print axioms PASoundness.PAtoCompactPAAddZeroNecessityFrame.equality_frame_right_graph
#print axioms PASoundness.PAtoCompactPAAddZeroNecessityFrame.equality_frame_right_graph_certificate
