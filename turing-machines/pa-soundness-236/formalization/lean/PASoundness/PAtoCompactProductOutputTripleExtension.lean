import PASoundness.PAtoCompactMultiplicationSingleTripleRetained
import PASoundness.PAtoCompactScopedActiveReplace

/-! Reallocate the single-triple adjunction used when collecting a
transported product graph. It keeps all old triples and inserts one selected
factor-pair/target-output triple, but is not the collection induction step. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputTripleExtension

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactMultiplicationSingleTripleExtension
open PASoundness.PAtoCompactMultiplicationSingleTripleRetained

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def retainedTriples : Formula := .all 3 (.all 4 (.all 5
  (.imp (tripleAt 6 3 4 5) (tripleAt 9 3 4 5))))
def oldStatement : Formula := .ex 11 (namedBoth (pairFormula 11 30 31) (.ex 12
  (namedBoth (pairFormula 12 11 32) (.ex 9 (namedBoth (namedAdjoin 6 12 9 16)
    (namedBoth (tripleAt 9 30 31 32) retainedTriples))))))
def newStatement : Formula := replace 32 33 (replace 6 58 oldStatement)
def newRetained : Formula := .all 3 (.all 4 (.all 5
  (.imp (tripleAt 58 3 4 5) (tripleAt 9 3 4 5))))

theorem new_statement_shape : newStatement = .ex 11 (namedBoth (pairFormula 11 30 31) (.ex 12
    (namedBoth (pairFormula 12 11 33) (.ex 9 (namedBoth (namedAdjoin 58 12 9 16)
      (namedBoth (tripleAt 9 30 31 33) newRetained)))))) := by decide

/-- Starting from any graph at 58, construct one extended graph at 9 with the
selected target triple and with every old triple preserved. -/
def selected_triple_extension : KDerivation newStatement.encode := by
  have h0 : KDerivation oldStatement.encode := by
    simpa [oldStatement, retainedTriples, oldTriplesRetained, namedAdjoin,
      namedBoth, namedEither, Formula.not, Formula.encode, adjoinCode, both, neg, either,
      PAtoCompactMultiplicationTripleAdjoinPreserve.tripleAt, tripleAt] using
        single_triple_extension_retaining_old
  have h1 := replace_derivation 6 58 oldStatement (by decide) (by decide) h0
  have h2 := replace_derivation 32 33 (replace 6 58 oldStatement) (by decide) (by decide) h1
  exact h2

theorem selected_triple_extension_certificate : theoremCode (certificate selected_triple_extension) =
    newStatement.encode := certificate_correct _

end PASoundness.PAtoCompactProductOutputTripleExtension

#print axioms PASoundness.PAtoCompactProductOutputTripleExtension.selected_triple_extension
#print axioms PASoundness.PAtoCompactProductOutputTripleExtension.selected_triple_extension_certificate
