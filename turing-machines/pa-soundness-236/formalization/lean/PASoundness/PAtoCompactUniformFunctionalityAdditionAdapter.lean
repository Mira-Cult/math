import PASoundness.PAtoCompactUniformFunctionalityFromFreshAddition
import PASoundness.PAtoCompactAdditionBinaryFunctionalGuarded

/-! Compose the fresh-base addition term-graph constructor with the guarded
structural recursion. Both imports are source drafts pending independent
Lean validation. This constructs no graph output transport. -/

namespace PASoundness.PAtoCompactUniformFunctionalityAdditionAdapter

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermSubstBinaryStep
open PASoundness.PAtoCompactEqSubstFromUniformGraphLaws
open PASoundness.PAtoCompactAdditionFreshFunctionalityInterface

/-- Specialize the arbitrary-mapping addition step to PA's identity variable
mapping. The underlying finite-K construction is an imported source draft. -/
noncomputable def freshAddition : FreshAddition := by
  intro t u b c p q e f g hbc hp hq ht hu hg hbe hce hpf hqf left right
  exact PASoundness.PAtoCompactAdditionBinaryFunctionalGuarded.addition_functionality_fresh
    id t u b c p q e f g hbc hp hq ht hu hg hbe hce hpf hqf left right

/-- Assemble the uniform guarded functionality family for every PA term.
This statement is as yet only a source draft until all dependencies pass an
independent Lean build and audit. -/
noncomputable def uniform_functionality : UniformFunctionality :=
  PASoundness.PAtoCompactUniformFunctionalityFromFreshAddition.uniform_functionality freshAddition

theorem uniform_functionality_certificate
    (g : Formula) (t : Peano.Term) (b p q : Nat) (hp : p < b) (hq : q < b)
    (ht : ∀ a ∈ t.varFinset, a < b) (hg : ∀ a ∈ g.free, a < b)
    (hd : ∀ a ∈ t.varFinset, KDerivation (imp g.encode (domainAt b a).encode)) :
    theoremCode (certificate (uniform_functionality g t b p q hp hq ht hg hd)) =
      imp g.encode (imp (termGraph id t p b).encode
        (imp (termGraph id t q b).encode (equivAt b p q).encode)) := certificate_correct _

end PASoundness.PAtoCompactUniformFunctionalityAdditionAdapter

#print axioms PASoundness.PAtoCompactUniformFunctionalityAdditionAdapter.freshAddition
#print axioms PASoundness.PAtoCompactUniformFunctionalityAdditionAdapter.uniform_functionality
#print axioms PASoundness.PAtoCompactUniformFunctionalityAdditionAdapter.uniform_functionality_certificate
