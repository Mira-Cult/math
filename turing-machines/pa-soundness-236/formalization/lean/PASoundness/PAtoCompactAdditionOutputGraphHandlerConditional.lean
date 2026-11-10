import PASoundness.PAtoCompactAdditionOutputGraphConditional
import PASoundness.PAtoCompactGuardedOutputReplacement

/-! Adapt a supplied per-base addition relation-output proof family to the
existing addition-root term-output interfaces. The relation family remains an
explicit input; this module does not construct it or prove a uniform law. -/
namespace PASoundness.PAtoCompactAdditionOutputGraphHandlerConditional
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermZeroGuarded
open PASoundness.PAtoCompactTermSubstPolyReplacement PASoundness.PAtoCompactGuardedOutputReplacement
open PASoundness.PAtoCompactAdditionOutputGraphConditional
set_option maxRecDepth 262144
set_option maxHeartbeats 0

/-- Per-base proof inputs with their source/target name bounds explicit. -/
def RelationFamily : Type := ∀ b q r, q < b → r < b → RelationOutput b q r

/-- A supplied operation proof family yields output transport at an addition
root. No output or functionality hypothesis for either child is assumed. -/
noncomputable def addition_output (family : RelationFamily) (t u : Peano.Term) :
    OutputTransport (binaryTerm true t u) := by
  intro b q r hq hr hv
  have hv' : ∀ a ∈ (binaryTerm true t u).varFinset, id a < b := by
    intro a ha
    simpa only [id_eq] using hv a ha
  exact addition_output_lift id t u b q r hq hr hv' (family b q r hq hr)

/-- The same supplied relation family yields the guard-conditioned interface. -/
noncomputable def guarded_addition_output (family : RelationFamily) (g : Formula) (t u : Peano.Term) :
    GuardedOutputTransport g (binaryTerm true t u) :=
  guard_unguarded_output g (binaryTerm true t u) (addition_output family t u)
end PASoundness.PAtoCompactAdditionOutputGraphHandlerConditional

#print axioms PASoundness.PAtoCompactAdditionOutputGraphHandlerConditional.addition_output
#print axioms PASoundness.PAtoCompactAdditionOutputGraphHandlerConditional.guarded_addition_output
