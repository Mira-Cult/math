import PASoundness.PAtoCompactPartialInversePredicate
import PASoundness.PAtoCompactUniformBase

/-! Exact globally quantified zero-base schema for the partial-inverse
predicate, with the shared induction bound name 10. This is a finite K proof;
it does not establish a successor step, global induction, or inverse graphs
at arbitrary prefixes. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseBaseTen
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactPartialInversePredicate PASoundness.PAtoCompactUniformBase
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The previously proved zero-prefix instance yields the exact universal
base schema at bound name 10, by a capture-safe 8-to-10 alpha conversion. -/
def exact_uniform_base : KDerivation (uniformBaseCode 30 10 9 predicate) := by
  let body := namedUniformBaseBody 30 8 9 predicate
  have hone : KDerivation (allCode 8 body.encode) := .generalize 8 empty_instance
  have halpha := (universalAlpha 8 10 body (by decide) (by decide) (by decide)).1
  have he : replace 8 10 body = namedUniformBaseBody 30 10 9 predicate := by decide
  rw [he] at halpha
  exact .mp hone halpha

theorem exact_uniform_base_certificate :
    theoremCode (certificate exact_uniform_base) = uniformBaseCode 30 10 9 predicate :=
  certificate_correct exact_uniform_base

end PASoundness.PAtoCompactPartialInverseBaseTen

#print axioms PASoundness.PAtoCompactPartialInverseBaseTen.exact_uniform_base
#print axioms PASoundness.PAtoCompactPartialInverseBaseTen.exact_uniform_base_certificate
