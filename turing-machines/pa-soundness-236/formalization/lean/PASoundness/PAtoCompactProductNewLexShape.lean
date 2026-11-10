import PASoundness.PAtoCompactProductCleanLexTransfer

/-! Exact named syntax of the lexicographic clause for a new multiplication
result. This records a syntactic identity only: it neither constructs the
product graph nor proves the comparison. All binder renamings are checked by
Lean; no semantic soundness or pair uniqueness is involved. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductNewLexShape
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactProductCleanLexTransfer
open PASoundness.PAtoCompactZeroSuccessor

/-- Literal lexicographic clause for source38, factor31, result45 and graph64. -/
def newLex : Formula := replace 2 45 (replace 1 31 (replace 0 38 (replace 6 64 lexFormula)))

/-- Exact six endpoint guards and two actual graph64 triples. -/
def newAntecedent : Formula := namedBoth (.member 38 3)
  (namedBoth (.member 31 4) (namedBoth (.member 45 5)
    (namedBoth (.member 38 7) (namedBoth (.member 31 8) (namedBoth (.member 45 9)
      (namedBoth (tripleAt 64 3 4 5) (tripleAt 64 7 8 9)))))))

def newPoint : Formula := .imp newAntecedent comparison

/-- The six quantifiers have precisely the intended fixed body and retain all
six membership guards. The replacement targets avoid the local binders. -/
theorem new_lex_shape : newLex =
    .all 3 (.all 4 (.all 5 (.all 7 (.all 8 (.all 9 newPoint))))) := by decide

/-- The new named comparison is the literal compact forward lex clause. -/
theorem comparison_encode : comparison.encode =
    both (imp (member 9 5) (either (member 7 3) (both (equal 3 7) (member 8 4))))
      (imp (either (member 7 3) (both (equal 3 7) (member 8 4))) (member 9 5)) := by rfl

end PASoundness.PAtoCompactProductNewLexShape
#print axioms PASoundness.PAtoCompactProductNewLexShape.new_lex_shape
#print axioms PASoundness.PAtoCompactProductNewLexShape.comparison_encode
