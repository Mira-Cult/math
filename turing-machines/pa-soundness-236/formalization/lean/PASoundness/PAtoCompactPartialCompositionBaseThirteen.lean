import PASoundness.PAtoCompactPartialCompositionPredicate
import PASoundness.PAtoCompactUniformBase

/-! Exact zero-base schema for partial-composition induction. This is a K
proof of the base only; it does not construct a successor extension or a
composition graph over arbitrary prefixes. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialCompositionBaseThirteen
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactPartialCompositionPredicate PASoundness.PAtoCompactUniformBase
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The empty-prefix K instance yields the global base schema for bound
prefix name 13, preserving all source, target, and input-graph parameters. -/
def exact_uniform_base : KDerivation (uniformBaseCode 30 13 11 predicate) := by
  let body := namedUniformBaseBody 30 10 11 predicate
  have hone : KDerivation (allCode 10 body.encode) := .generalize 10 empty_instance
  have halpha := (universalAlpha 10 13 body (by decide) (by decide) (by decide)).1
  have he : replace 10 13 body = namedUniformBaseBody 30 13 11 predicate := by decide
  rw [he] at halpha
  exact .mp hone halpha

theorem exact_uniform_base_certificate :
    theoremCode (certificate exact_uniform_base) = uniformBaseCode 30 13 11 predicate :=
  certificate_correct exact_uniform_base

end PASoundness.PAtoCompactPartialCompositionBaseThirteen

#print axioms PASoundness.PAtoCompactPartialCompositionBaseThirteen.exact_uniform_base
#print axioms PASoundness.PAtoCompactPartialCompositionBaseThirteen.exact_uniform_base_certificate
