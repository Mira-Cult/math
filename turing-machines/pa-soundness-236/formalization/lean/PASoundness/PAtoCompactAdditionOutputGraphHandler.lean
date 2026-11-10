import PASoundness.PAtoCompactAdditionOutputUniformRelation
import PASoundness.PAtoCompactAdditionOutputGraphHandlerConditional

/-! Specialize the finite-K addition relation-output proof to the existing
addition-root graph interfaces. This noncomputable proof-data construction
has no caller-supplied proof input; the all-term family remains separate. -/
namespace PASoundness.PAtoCompactAdditionOutputGraphHandler
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermZeroGuarded
open PASoundness.PAtoCompactTermSubstPolyReplacement PASoundness.PAtoCompactGuardedOutputReplacement
open PASoundness.PAtoCompactAdditionOutputUniformRelation
open PASoundness.PAtoCompactAdditionOutputGraphHandlerConditional
set_option maxRecDepth 262144
set_option maxHeartbeats 0

/-- The graph allocator bounds imply all four name bounds for the operation
proof: the child outputs are the syntactic names b and b+1. -/
noncomputable def addition_relation_family : RelationFamily := by
  intro b q r hq hr
  exact output_relation b b (b+1) q r (by omega) (by omega) (by omega) (by omega)

/-- Every addition-root term has the existing unguarded output-transport
interface, without caller-supplied child or operation proof inputs. -/
noncomputable def addition_root_output (t u : Peano.Term) :
    OutputTransport (binaryTerm true t u) :=
  addition_output addition_relation_family t u

/-- The addition-root proof also gives the existing guard-conditioned output
interface for any guard. -/
noncomputable def guarded_addition_root_output (g : Formula) (t u : Peano.Term) :
    GuardedOutputTransport g (binaryTerm true t u) :=
  guarded_addition_output addition_relation_family g t u
end PASoundness.PAtoCompactAdditionOutputGraphHandler

#print axioms PASoundness.PAtoCompactAdditionOutputGraphHandler.addition_relation_family
#print axioms PASoundness.PAtoCompactAdditionOutputGraphHandler.addition_root_output
#print axioms PASoundness.PAtoCompactAdditionOutputGraphHandler.guarded_addition_root_output
