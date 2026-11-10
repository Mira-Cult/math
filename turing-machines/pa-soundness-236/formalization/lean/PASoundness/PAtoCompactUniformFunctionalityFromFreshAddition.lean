import PASoundness.PAtoCompactGuardFunctionalityInduction
import PASoundness.PAtoCompactSuccGuardFunctionalityStep
import PASoundness.PAtoCompactAdditionGuardFunctionalityAssumed

/-! Reduce uniform guarded functionality to the explicitly supplied fresh-base
addition family. No addition proof or output-transport family is constructed
by this adapter. -/

namespace PASoundness.PAtoCompactUniformFunctionalityFromFreshAddition

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermSubstBinaryStep
open PASoundness.PAtoCompactTermSubstPolyReplacement
open PASoundness.PAtoCompactEqSubstFromUniformGraphLaws
open PASoundness.PAtoCompactAdditionFreshFunctionalityInterface
open PASoundness.PAtoCompactGuardFunctionalityInduction

/-- Existing successor and multiplication constructors and the supplied
fresh-base addition family give the structural node steps. -/
noncomputable def nodeSteps (fresh : FreshAddition) : NodeSteps where
  successor := PASoundness.PAtoCompactSuccGuardFunctionalityStep.successor_guard_functionality
  addition := by
    intro g t u ht hu
    simpa [Peano.add, binaryTerm] using
      PASoundness.PAtoCompactAdditionGuardFunctionalityAssumed.addition_guard_functionality
        fresh g t u ht hu

/-- Uniform functionality for every guard and PA term, conditional on the
explicit fresh-base addition proof family. -/
noncomputable def uniform_functionality (fresh : FreshAddition) : UniformFunctionality :=
  uniform (nodeSteps fresh)

/-- The output of the conditional recursion is finite K proof data for the
literal guarded graph-functionality formula. -/
theorem uniform_functionality_certificate (fresh : FreshAddition)
    (g : Formula) (t : Peano.Term) (b p q : Nat) (hp : p < b) (hq : q < b)
    (ht : ∀ a ∈ t.varFinset, a < b) (hg : ∀ a ∈ g.free, a < b)
    (hd : ∀ a ∈ t.varFinset, KDerivation (imp g.encode (domainAt b a).encode)) :
    theoremCode (certificate (uniform_functionality fresh g t b p q hp hq ht hg hd)) =
      imp g.encode (imp (termGraph id t p b).encode
        (imp (termGraph id t q b).encode (equivAt b p q).encode)) := certificate_correct _

end PASoundness.PAtoCompactUniformFunctionalityFromFreshAddition

#print axioms PASoundness.PAtoCompactUniformFunctionalityFromFreshAddition.nodeSteps
#print axioms PASoundness.PAtoCompactUniformFunctionalityFromFreshAddition.uniform_functionality
#print axioms PASoundness.PAtoCompactUniformFunctionalityFromFreshAddition.uniform_functionality_certificate
