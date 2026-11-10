import PASoundness.PAtoCompactCompositionForwardEndpoint
import PASoundness.PAtoCompactCompositionPathVacuity
import PASoundness.PAtoCompactCompositionPathElim

/-! Existential middle-witness elimination for the supplied endpoint forward
coverage. The selected uniqueness clauses and new edge remain explicit
premises; no graph construction, choice function, or induction is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCompositionForwardEndpointExists
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactPartialCompositionOutputUnique PASoundness.PAtoCompactCompositionForwardEndpoint
open PASoundness.PAtoCompactCompositionPathVacuity PASoundness.PAtoCompactCompositionPathElim
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- At fixed middle name 4, the endpoint-context assumptions and path body
suffice for the supplied new graph edge. -/
def endpoint_point : KDerivation (imp premises.encode (imp pathBody target)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [pathBody,premises.encode]
  have hp : Context Γ pathBody := Context.head _ _
  have hu : Context Γ premises.encode := .hypothesis (by simp [Γ])
  have hf : Context Γ firstUnique.encode := Context.conjunctionLeft hu
  have htail := Context.conjunctionRight hu
  have hs : Context Γ secondUnique.encode := Context.conjunctionLeft htail
  have htail := Context.conjunctionRight htail
  have he : Context Γ (equal 2 10) := Context.conjunctionLeft htail
  have htail := Context.conjunctionRight htail
  have hc : Context Γ (member 8 3) := Context.conjunctionLeft htail
  have hn : Context Γ (graphFormula 17 10 12).encode := Context.conjunctionRight htail
  have hb : Context Γ (member 1 4) := Context.conjunctionLeft hp
  have hg1 : Context Γ (graphFormula 6 2 4).encode := Context.conjunctionLeft (Context.conjunctionRight hp)
  have hg2 : Context Γ (graphFormula 7 4 3).encode := Context.conjunctionRight (Context.conjunctionRight hp)
  exact .mp hn (.mp hg2 (.mp hc (.mp hg1 (.mp hb (.mp he (.mp hs (.mp hf (.closed endpoint_coverage))))))))

/-- Eliminate the queried path's middle witness using proved vacuity of the
context at name 4. -/
def endpoint_path : KDerivation (imp premises.encode (imp (existsCode 4 pathBody) target)) :=
  eliminate_path premises.encode premises_vacuity endpoint_point

theorem endpoint_path_certificate : theoremCode (certificate endpoint_path) =
    imp premises.encode (imp (existsCode 4 pathBody) target) := certificate_correct endpoint_path

end PASoundness.PAtoCompactCompositionForwardEndpointExists

#print axioms PASoundness.PAtoCompactCompositionForwardEndpointExists.endpoint_path
#print axioms PASoundness.PAtoCompactCompositionForwardEndpointExists.endpoint_path_certificate
