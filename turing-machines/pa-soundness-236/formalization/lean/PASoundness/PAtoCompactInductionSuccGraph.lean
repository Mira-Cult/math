import PASoundness.PAtoCompactSuccTermTotality
import PASoundness.PAtoCompactRawSuccessorBinderBridge
import PASoundness.PAtoCompactCandidateDynamicReflexivity

/-! The named successor of a candidate is a value of the literal successor
term graph. This is finite K proof data and does not establish substitution
compatibility for arbitrary PA formulas or the PA induction axiom. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactInductionSuccGraph
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactSuccTermTotality PASoundness.PAtoCompactVariableTermTotality
open PASoundness.PAtoCompactCandidateDynamicReflexivity PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactRawSuccessorBinderBridge

/-- If both named endpoints are candidates and z is the literal successor of
 y, then z satisfies the generated graph for the PA term S(y). The successor
membership-test name is distinct from the endpoint names; the endpoints may
represent equal objects and no semantic soundness theorem is used. -/
def successor_term_graph (base y z w : Nat) (hy : y < base) (hz : z < base) (hwy : w ≠ y) (hwz : w ≠ z) :
    KDerivation (imp (domainAt base y).encode
      (imp (domainAt base z).encode
        (imp (successorCode y z w)
          (termGraph (fun n : Nat => n) (Peano.succ (.var y)) z base).encode))) := by
  have htransport := domainAt_transport base (base+64) y (by omega) (by omega)
  have hrefl := dynamic_reflexive (base+64) y (by omega)
  have hvar := variable_graph_at_source (base+64) y hrefl
  have hterm : KDerivation (imp (domainAt base y).encode
      (termGraph (fun n : Nat => n) (.var y : Peano.Term) y (base+64)).encode) := by
    simpa only [termGraph] using compose htransport hvar
  have hq := quotient_of_arbitrary_raw base y z w (by omega) hz hwy hwz
  have hg := succTerm_from_witness (fun n : Nat => n) (.var y : Peano.Term)
    base z y hz hy (by
      intro a ha
      have he : a = y := by simpa using ha
      simpa only [he] using hy)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [successorCode y z w, (domainAt base z).encode, (domainAt base y).encode]
  have hs : Context Γ (successorCode y z w) := .hypothesis (by simp [Γ])
  have hz' : Context Γ (domainAt base z).encode := .hypothesis (by simp [Γ])
  have hy' : Context Γ (domainAt base y).encode := .hypothesis (by simp [Γ])
  have hvar' := Context.mp hy' (.closed hterm)
  have hq' := Context.mp hz' (Context.mp hs (Context.mp hy' (.closed hq)))
  have hgraph := Context.mp hq' (Context.mp hvar' (Context.mp hz' (.closed hg)))
  simpa only [Peano.succ] using hgraph

theorem successor_term_graph_certificate (base y z w : Nat) (hy : y < base) (hz : z < base) (hwy : w ≠ y) (hwz : w ≠ z) :
    theoremCode (certificate (successor_term_graph base y z w hy hz hwy hwz)) =
      imp (domainAt base y).encode (imp (domainAt base z).encode
        (imp (successorCode y z w)
          (termGraph (fun n : Nat => n) (Peano.succ (.var y)) z base).encode)) :=
  certificate_correct _
end PASoundness.PAtoCompactInductionSuccGraph

#print axioms PASoundness.PAtoCompactInductionSuccGraph.successor_term_graph
#print axioms PASoundness.PAtoCompactInductionSuccGraph.successor_term_graph_certificate
