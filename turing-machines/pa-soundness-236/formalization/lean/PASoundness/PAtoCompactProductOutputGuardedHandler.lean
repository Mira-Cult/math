import PASoundness.PAtoCompactProductOutputTermNode
import PASoundness.PAtoCompactGuardedOutputReplacement

/-! Adapt the product-node output lift to the existing unguarded and guarded
term-output interfaces used by the equality-substitution bridge. This file
only handles a product-root term; it does not establish the all-term family. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputGuardedHandler

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermZeroGuarded
open PASoundness.PAtoCompactTermSubstPolyReplacement PASoundness.PAtoCompactGuardedOutputReplacement
open PASoundness.PAtoCompactProductOutputTermNode

/-- A product-root term satisfies the unguarded output interface without
assuming output laws for its children. -/
noncomputable def product_output (t u : Peano.Term) : OutputTransport (binaryTerm false t u) := by
  intro b q r hq hr hv
  have hv' : ∀ a ∈ (binaryTerm false t u).varFinset, id a < b := by
    intro a ha
    simpa only [id_eq] using hv a ha
  exact mul_output_lift id t u b q r hq hr hv'

/-- The same product-root law supplies the standard guarded bridge input. -/
noncomputable def guarded_product_output (g : Formula) (t u : Peano.Term) :
    GuardedOutputTransport g (binaryTerm false t u) :=
  guard_unguarded_output g (binaryTerm false t u) (product_output t u)

end PASoundness.PAtoCompactProductOutputGuardedHandler

#print axioms PASoundness.PAtoCompactProductOutputGuardedHandler.product_output
#print axioms PASoundness.PAtoCompactProductOutputGuardedHandler.guarded_product_output
