import PASoundness.PAtoCompactProductOutputPreimagePoint
import PASoundness.PAtoCompactProductMatchSourceForwardWitness

/-! Recover a forward product witness at the exact source output and
coordinates supplied by a reverse witness. The product matrix and source
output membership remain explicit; this is not graph collection. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputForwardFromReverse

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactProductOutputImagePoint PASoundness.PAtoCompactProductOutputPreimagePoint
open PASoundness.PAtoCompactProductMatchSourceForwardWitness
open PASoundness.PAtoCompactMultiplicationCandidate

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def relocatedForwardFrame : Formula := replace 2 0 (replace 1 81 (replace 0 80
  PAtoCompactProductMatchSourceForwardWitness.sourceFrame))
def selectedTriple : Formula := replace 2 0 (replace 1 81 (replace 0 80 (tripleFormula 30 31 32)))
def reverseTail : Formula := replace 2 0 (replace 1 81 (replace 0 80
  (replace 4 31 (replace 3 30 (replace 5 32
    (.all 7 (.all 8 (.imp (namedBoth (.member 0 7) (namedBoth (.member 1 8)
      (tripleFormula 7 8 5))) (namedBoth (.equal 7 3) (.equal 8 4))))))))))

theorem forward_frame_shape : relocatedForwardFrame = .imp sourceMatrix
    (.imp (.member 80 30) (.imp (.member 81 31) (.imp (.member 0 32)
      (.imp selectedTriple sourceBody)))) := by decide

theorem reverse_body_shape : reverseBody = namedBoth (.member 80 30)
    (namedBoth (.member 81 31) (namedBoth selectedTriple reverseTail)) := by decide

def forward_from_reverse : KDerivation (imp sourceMatrix.encode (imp (member 0 32)
    (imp reverseBody.encode sourceBody.encode))) := by
  have h0 : KDerivation PAtoCompactProductMatchSourceForwardWitness.sourceFrame.encode := by
    simpa [PAtoCompactProductMatchSourceForwardWitness.sourceFrame, CompactNamed.Formula.encode] using source_forward_witness
  have h1 := replace_derivation 0 80 PAtoCompactProductMatchSourceForwardWitness.sourceFrame (by decide) (by decide) h0
  have h2 := replace_derivation 1 81 (replace 0 80 PAtoCompactProductMatchSourceForwardWitness.sourceFrame) (by decide) (by decide) h1
  have h3 := replace_derivation 2 0 (replace 1 81 (replace 0 80 PAtoCompactProductMatchSourceForwardWitness.sourceFrame)) (by decide) (by decide) h2
  have hf : KDerivation (imp sourceMatrix.encode (imp (member 80 30) (imp (member 81 31)
      (imp (member 0 32) (imp selectedTriple.encode sourceBody.encode))))) := by
    change KDerivation relocatedForwardFrame.encode at h3
    rw [forward_frame_shape] at h3
    simpa only [CompactNamed.Formula.encode] using h3
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [reverseBody.encode, member 0 32, sourceMatrix.encode]
  have hr : Context Γ reverseBody.encode := .head _ _
  have ho : Context Γ (member 0 32) := .hypothesis (by simp [Γ])
  have hm : Context Γ sourceMatrix.encode := .hypothesis (by simp [Γ])
  have hr' : Context Γ (both (member 80 30) (both (member 81 31)
      (both selectedTriple.encode reverseTail.encode))) := by
    simpa [reverse_body_shape, namedBoth, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, both, neg] using hr
  have ha := Context.conjunctionLeft hr'
  have hb := Context.conjunctionLeft (Context.conjunctionRight hr')
  have ht := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hr'))
  exact .mp ht (.mp ho (.mp hb (.mp ha (.mp hm (.closed hf)))))

theorem forward_from_reverse_certificate : theoremCode (certificate forward_from_reverse) =
    imp sourceMatrix.encode (imp (member 0 32) (imp reverseBody.encode sourceBody.encode)) := certificate_correct _

end PASoundness.PAtoCompactProductOutputForwardFromReverse

#print axioms PASoundness.PAtoCompactProductOutputForwardFromReverse.forward_from_reverse
#print axioms PASoundness.PAtoCompactProductOutputForwardFromReverse.forward_from_reverse_certificate
