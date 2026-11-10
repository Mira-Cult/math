import PASoundness.PAtoCompactProductOutputReverseFromSource
import PASoundness.PAtoCompactProductOutputImageUnique

/-! A retained forward source/image body and its guarded factor inputs yield
the source reverse-coordinate witness at the same source output. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputPairedReverse

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactProductOutputImagePoint PASoundness.PAtoCompactProductOutputReverseCoverage
open PASoundness.PAtoCompactProductOutputReverseFromSource PASoundness.PAtoCompactProductOutputCollectionInsideConditional

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def paired_reverse : KDerivation (imp assumptions.encode (imp (member 43 30)
    (imp (member 44 31) (imp PAtoCompactProductOutputImagePoint.pairedBody.encode relocatedReverse.encode)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [PAtoCompactProductOutputImagePoint.pairedBody.encode,member 44 31,member 43 30,assumptions.encode]
  have hp : Context Γ PAtoCompactProductOutputImagePoint.pairedBody.encode := .head _ _
  have hy : Context Γ (member 44 31) := .hypothesis (by simp [Γ])
  have hx : Context Γ (member 43 30) := .hypothesis (by simp [Γ])
  have ha : Context Γ assumptions.encode := .hypothesis (by simp [Γ])
  have ha' : Context Γ (both relocatedMatrix.encode PAtoCompactProductMatchFactorImages.firstBijection.encode) := by
    simpa [assumptions, relocatedMatrix, namedBoth, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, both, neg] using ha
  have hp' : Context Γ (both sourceBody.encode imageBody.encode) := by
    simpa [PAtoCompactProductOutputImagePoint.pairedBody, namedBoth, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, both, neg] using hp
  have hs : Context Γ (both (member 0 32) (both (tripleFormula 30 31 32).encode
      (Formula.all 9 PAtoCompactProductOutputImageUnique.sourceUnique).encode)) := by
    simpa [PAtoCompactProductOutputImageUnique.source_shape, namedBoth, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, both, neg] using Context.conjunctionLeft hp'
  exact .mp (Context.conjunctionLeft (Context.conjunctionRight hs))
    (.mp (Context.conjunctionLeft hs) (.mp hy (.mp hx
      (.mp (Context.conjunctionLeft ha') (.closed reverse_from_source)))))

theorem paired_reverse_certificate : theoremCode (certificate paired_reverse) =
    imp assumptions.encode (imp (member 43 30) (imp (member 44 31)
      (imp PAtoCompactProductOutputImagePoint.pairedBody.encode relocatedReverse.encode))) := certificate_correct _

end PASoundness.PAtoCompactProductOutputPairedReverse

#print axioms PASoundness.PAtoCompactProductOutputPairedReverse.paired_reverse
#print axioms PASoundness.PAtoCompactProductOutputPairedReverse.paired_reverse_certificate
