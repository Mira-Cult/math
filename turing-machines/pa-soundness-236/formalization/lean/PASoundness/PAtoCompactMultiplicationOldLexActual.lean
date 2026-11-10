import PASoundness.PAtoCompactProductOldLexBoth
import PASoundness.PAtoCompactMultiplicationLexSharedContext
import PASoundness.PAtoCompactMultiplicationSameRowLex

/-! Capture-safe relocation of the old product's two pointwise lexicographic
comparisons to the multiplication construction's actual input/result names.
All six old-domain endpoint memberships and both old graph triples remain
explicit. This does not transport outputs through a cut isomorphism, assert
new graph order, multiplication totality, or PA soundness. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationOldLexActual
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactProductCleanLexTransfer PASoundness.PAtoCompactProductOldLexPoint
open PASoundness.PAtoCompactProductOldLexSwapped PASoundness.PAtoCompactProductOldLexBoth
open PASoundness.PAtoCompactMultiplicationLexSharedContext
open PASoundness.PAtoCompactMultiplicationSameRowLex PASoundness.PAtoCompactZeroSuccessor
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Both old triples have all three endpoints in their actual old domains. -/
def oldAntecedent : Formula := namedBoth (.member 30 3)
  (namedBoth (.member 31 4) (namedBoth (.member 32 5)
    (namedBoth (.member 30 7) (namedBoth (.member 31 8) (namedBoth (.member 32 9)
      (namedBoth (tripleAt 10 3 4 5) (tripleAt 10 7 8 9)))))))

private def f : Formula := .imp oldMatrixAtTen (.imp (antecedent 10)
  (namedBoth comparison reverseComparison))
private def f30 : Formula := replace 0 30 f
private def f31 : Formula := replace 1 31 f30

private def at_base : KDerivation f.encode := by
  simpa [f, namedBoth, Formula.not, Formula.encode, both, neg] using old_old_both

private def at30 : KDerivation f30.encode := by
  have hi := universalInstance 0 30 f (by decide) (by decide) (by decide)
  exact .mp (.generalize 0 at_base) hi

private def at31 : KDerivation f31.encode := by
  have hi := universalInstance 1 31 f30 (by decide) (by decide) (by decide)
  exact .mp (.generalize 1 at30) hi

/-- The exact old matrix in the shared lex context entails both tuple
comparisons for two old graph triples, guarded by all six endpoint memberships.
The comparisons concern the old outputs 5 and 9. -/
def old_old_actual : KDerivation (imp oldMatrixActual.encode
    (imp oldAntecedent.encode (both forwardClause reverseClause))) := by
  have hi := universalInstance 2 32 f31 (by decide) (by decide) (by decide)
  have h := KDerivation.mp (.generalize 2 at31) hi
  have shape : replace 2 32 f31 = .imp oldMatrixActual
      (.imp oldAntecedent (namedBoth comparison reverseComparison)) := by decide
  rw [shape] at h
  simpa [namedBoth,namedEither,Formula.not,Formula.encode,both,neg,either,
    comparison,reverseComparison,forwardClause,reverseClause,forwardLex,reverseLex] using h

theorem old_old_actual_certificate : theoremCode (certificate old_old_actual) =
    imp oldMatrixActual.encode (imp oldAntecedent.encode (both forwardClause reverseClause)) :=
  certificate_correct old_old_actual
end PASoundness.PAtoCompactMultiplicationOldLexActual
#print axioms PASoundness.PAtoCompactMultiplicationOldLexActual.old_old_actual
#print axioms PASoundness.PAtoCompactMultiplicationOldLexActual.old_old_actual_certificate
