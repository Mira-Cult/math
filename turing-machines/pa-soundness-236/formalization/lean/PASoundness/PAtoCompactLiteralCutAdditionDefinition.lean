import PASoundness.PAtoCompactOrdinalAddition
import PASoundness.PAtoCompactTermTranslation
import PASoundness.PAtoCompactZeroSuccessor

/-! The strengthened addition relation retains the first summand literally
as the cut. It says the cut equals or belongs to the result, the displayed
suffix is the result filtered outside that cut, and the second summand is
isomorphic to that suffix. No existence, functionality, or PA soundness is
asserted here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLiteralCutAdditionDefinition
open PASoundness.CompactNamed PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactZeroSuccessor

/-- First input 30 is the literal cut; second input 31 and output 32 use the
same names as the existing candidate addition formula. -/
def literalCut : Formula := .ex 34
  (namedBoth (namedEither (.equal 30 32) (.member 32 30))
    (namedBoth (replace 33 30 suffixFormula) (PAtoCompactOrdinalAddition.equivAt 31 34)))

/-- The candidate-guarded induction property, at second-input name 31. -/
def predicate : Formula := .imp (domainAt 100 30)
  (.ex 32 (andF (domainAt 100 32) literalCut))

theorem literalCut_free : literalCut.free = {30,31,32} := by decide

theorem predicate_free : predicate.free = {30,31} := by decide

end PASoundness.PAtoCompactLiteralCutAdditionDefinition
#print axioms PASoundness.PAtoCompactLiteralCutAdditionDefinition.literalCut_free
#print axioms PASoundness.PAtoCompactLiteralCutAdditionDefinition.predicate_free
