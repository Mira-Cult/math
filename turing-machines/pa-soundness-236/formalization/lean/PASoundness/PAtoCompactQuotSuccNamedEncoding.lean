import PASoundness.PAtoCompactTermSuccessorIdentity
import PASoundness.PAtoCompactQuotSuccWitnessFresh

/-! Exact encoding agreement between the independently constructed direct
named quotient-successor witness body and the literal quotient-successor
formula. This is an encoding identity only: no substitution, K derivation,
quotient axiom, or PA interpretation follows here. -/
namespace PASoundness.PAtoCompactQuotSuccNamedEncoding
open PASoundness.CompactNamed
open PASoundness.PAtoCompactQuotientSuccessor
open PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactTermSuccessorIdentity
open PASoundness.PAtoCompactQuotSuccWitnessFresh

/-- The two direct named templates agree as syntax, before either numeric
encoding is evaluated. -/
theorem template_body_shape : successorTemplate = Formula.ex 7 namedBody := rfl

/-- The direct named body has exactly the unchanged quotient-successor code. -/
theorem named_successor_encode : successorFormula.encode = (Formula.ex 7 namedBody).encode :=
  successorTemplate_encode.symm.trans (congrArg Formula.encode template_body_shape)

end PASoundness.PAtoCompactQuotSuccNamedEncoding

#print axioms PASoundness.PAtoCompactQuotSuccNamedEncoding.named_successor_encode
