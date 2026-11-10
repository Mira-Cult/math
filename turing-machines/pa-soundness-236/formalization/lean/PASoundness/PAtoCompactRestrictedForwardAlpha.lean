import PASoundness.PAtoCompactRestrictedForwardWitnessAll
import PASoundness.CompactFreshen

/-! Capture-safe staging of the forward-bijection clause for the restricted
source 2, target 5 and graph 8. The literal source name must be changed only
after the original input binder has been alpha-renamed. This module makes no
claim about the complete restricted isomorphism or quotient cancellation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictedForwardAlpha
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactBijectionForwardAtSeven PASoundness.PAtoCompactRestrictedForwardUnique
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Original forward-bijection clause before name alignment. -/
def originalBody : Formula := .imp (.member 0 2) (.ex 3 witnessAtTwo)
def originalForward : Formula := .all 2 originalBody

/-- Rename the original input binder 2 to the fresh name 7 before changing
the free source name 0 to 2. -/
def preparedForward : Formula := .all 7 (replace 2 7 originalBody)

/-- After binder preparation, map free source 0, target 1 and graph 6 to
their displayed old-domain names 2,5,8. -/
def stagedForward : Formula :=
  replace 6 8 (replace 1 5 (replace 0 2 preparedForward))

/-- The exact already-derived guarded forward clause. -/
def restrictedForward : Formula := .all 7
  (.imp (.member 2 7) (.ex 3 restrictedWitness))

/-- The first step is an actual bidirectional K alpha conversion. -/
def prepare_alpha : ProofEquiv originalForward preparedForward :=
  ProofEquiv.alphaAll 2 7 originalBody (by decide) (by decide) (by decide)

/-- Only after that alpha step, the explicit source/target/graph replacements
produce exactly the same named formula as the derived restricted clause. -/
theorem staged_syntax : stagedForward = restrictedForward := by decide

/-- The target named formula has exactly the numeric code of the derived
forward clause with input binder 7 and output binder 3. -/
theorem restricted_forward_code : restrictedForward.encode =
    allCode 7 (imp (member 2 7) (existsCode 3 restrictedWitness.encode)) := rfl

theorem prepare_alpha_forward_certificate :
    theoremCode (certificate prepare_alpha.forward) = imp originalForward.encode preparedForward.encode :=
  certificate_correct prepare_alpha.forward

theorem prepare_alpha_backward_certificate :
    theoremCode (certificate prepare_alpha.backward) = imp preparedForward.encode originalForward.encode :=
  certificate_correct prepare_alpha.backward

end PASoundness.PAtoCompactRestrictedForwardAlpha

#print axioms PASoundness.PAtoCompactRestrictedForwardAlpha.prepare_alpha_forward_certificate
#print axioms PASoundness.PAtoCompactRestrictedForwardAlpha.prepare_alpha_backward_certificate
#print axioms PASoundness.PAtoCompactRestrictedForwardAlpha.staged_syntax
