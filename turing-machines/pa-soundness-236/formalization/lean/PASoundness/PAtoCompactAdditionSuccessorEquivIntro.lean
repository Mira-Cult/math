import PASoundness.PAtoCompactOrdinalAddition
import PASoundness.PAtoCompactSuccCongruenceData
import PASoundness.CompactQuantifiers

/-! Introduction of the canonical quotient-equivalence formula from the
literal proposed addition-successor graph matrix. The graph at name 9 is
supplied as a K premise; no graph existence, arithmetic totality or PA proof
translation is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionSuccessorEquivIntro
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrdinalAddition PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactSuccCongruenceData PASoundness.PAtoCompactZeroSuccessor
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Matrix for the new source 38, new suffix 40 and supplied graph 9. -/
def matrixNamed : Formula := replace 8 40 (replace 7 38 (namedBoth newBijection newOrder))
private def canonicalBody : Formula := replace 1 40 (replace 0 38 (namedBoth bijectionFormula orderFormula))
private theorem body_identity : replace 6 9 canonicalBody = matrixNamed := by decide
private theorem equiv_identity : equivAt 38 40 = .ex 6 canonicalBody := by decide

/-- A supplied graph satisfying the full new matrix yields the actual quotient
formula, with graph bound at its canonical label. The binder transport is
capture-safe; it assumes neither existence nor transitivity. -/
def matrix_to_equiv : KDerivation (imp matrixNamed.encode (equivAt 38 40).encode) := by
  have hi : KDerivation (imp matrixNamed.encode (existsCode 9 matrixNamed.encode)) := by
    exact CompactNamed.existsIntroduce 9 matrixNamed (by decide)
  have ha := (CompactNamed.existentialAlpha 6 9 canonicalBody (by decide) (by decide) (by decide)).2
  rw [body_identity] at ha
  have ht : KDerivation (imp (existsCode 9 matrixNamed.encode) (equivAt 38 40).encode) := by
    simpa only [equiv_identity, Formula.encode] using ha
  exact compose hi ht

theorem matrix_to_equiv_certificate : theoremCode (certificate matrix_to_equiv) =
    imp matrixNamed.encode (equivAt 38 40).encode := certificate_correct matrix_to_equiv
end PASoundness.PAtoCompactAdditionSuccessorEquivIntro
#print axioms PASoundness.PAtoCompactAdditionSuccessorEquivIntro.matrix_to_equiv
#print axioms PASoundness.PAtoCompactAdditionSuccessorEquivIntro.matrix_to_equiv_certificate
