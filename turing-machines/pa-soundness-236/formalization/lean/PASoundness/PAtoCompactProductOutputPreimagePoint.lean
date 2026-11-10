import PASoundness.PAtoCompactProductOutputImagePoint
import PASoundness.PAtoCompactProductMatchReverseFactors

/-! For a displayed target-output member, retain one isomorphism preimage and
its source-product coordinates. This is pointwise preparation for collecting
a transported product graph, not a target product-graph construction. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputPreimagePoint

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactProductMatchPointWitness PASoundness.PAtoCompactProductMatchFactorImages
open PASoundness.PAtoCompactProductMatchReverseFactors PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactProductOutputImagePoint

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def reverseBody : Formula := replace 2 0 (replace 1 81 (replace 0 80 selectedReverseBody))
def reverseFrame : Formula := .imp productMatrix (.imp (.member 2 32)
  (.ex 30 (.ex 31 selectedReverseBody)))
def relocatedFrame : Formula := .imp sourceMatrix (.imp (.member 0 32)
  (.ex 30 (.ex 31 reverseBody)))
def preimage32 : Formula := replace 30 32 majorPreimage
def pairedBody : Formula := namedBoth preimage32 reverseBody
def guard : Formula := namedBoth sourceMatrix firstBijection

theorem reverse_frame_shape : replace 2 0 (replace 1 81 (replace 0 80 reverseFrame)) = relocatedFrame := by decide
theorem preimage_shape : preimage32 = namedBoth (.member 0 32)
    (namedBoth (PAtoCompactOrderIsomorphism.graphFormula 40 32 33)
      (.all 4 (.imp (namedBoth (.member 0 4) (PAtoCompactOrderIsomorphism.graphFormula 40 4 33)) (.equal 4 32)))) := by decide

def source_coordinates : KDerivation (imp sourceMatrix.encode (imp (member 0 32)
    (existsCode 30 (existsCode 31 reverseBody.encode)))) := by
  have h0 : KDerivation reverseFrame.encode := by simpa [reverseFrame, Formula.encode] using reverse_coordinates
  have h1 := replace_derivation 0 80 reverseFrame (by decide) (by decide) h0
  have h2 := replace_derivation 1 81 (replace 0 80 reverseFrame) (by decide) (by decide) h1
  have h3 := replace_derivation 2 0 (replace 1 81 (replace 0 80 reverseFrame)) (by decide) (by decide) h2
  rw [reverse_frame_shape] at h3
  simpa [relocatedFrame, Formula.encode] using h3

def output_preimage : KDerivation (imp firstBijection.encode (imp (member 42 33)
    (existsCode 32 preimage32.encode))) := by
  have ha := (existentialAlpha 30 32 majorPreimage (by decide) (by decide) (by decide)).1
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 42 33,firstBijection.encode]
  have hy : Context Γ (member 42 33) := .head _ _
  have hb : Context Γ firstBijection.encode := .hypothesis (by simp [Γ])
  have hw := Context.mp hy (Context.mp hb (.closed major_preimage))
  simpa [Γ, preimage32] using Context.mp hw (.closed ha)

def coordinates_retained : KDerivation (imp guard.encode (imp preimage32.encode
    (existsCode 30 (existsCode 31 pairedBody.encode)))) := by
  have hpoint : KDerivation (imp preimage32.encode (imp reverseBody.encode pairedBody.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [reverseBody.encode,preimage32.encode]
    have hr : Context Γ reverseBody.encode := .head _ _
    have hp : Context Γ preimage32.encode := .hypothesis (by simp [Γ])
    simpa [Γ, pairedBody, namedBoth, Formula.not, Formula.encode, both, neg] using Context.conjunctionIntro hp hr
  have h31 := conditionalExistsCongr 31 (preimage32.vacuity 31 (by decide)) hpoint
  have h30 := conditionalExistsCongr 30 (preimage32.vacuity 30 (by decide)) h31
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [preimage32.encode,guard.encode]
  have hp : Context Γ preimage32.encode := .head _ _
  have hg : Context Γ guard.encode := .hypothesis (by simp [Γ])
  have hg' : Context Γ (both sourceMatrix.encode firstBijection.encode) := by
    simpa [guard, namedBoth, Formula.not, Formula.encode, both, neg] using hg
  have hp' : Context Γ (both (member 0 32)
      (both (PAtoCompactOrderIsomorphism.graphFormula 40 32 33).encode
        (Formula.all 4 (.imp (namedBoth (.member 0 4)
          (PAtoCompactOrderIsomorphism.graphFormula 40 4 33)) (.equal 4 32))).encode)) := by
    simpa [preimage_shape, namedBoth, Formula.not, Formula.encode, both, neg] using hp
  have hw := Context.mp (Context.conjunctionLeft hp')
    (Context.mp (Context.conjunctionLeft hg') (.closed source_coordinates))
  simpa [Γ] using Context.mp hw (Context.mp hp (.closed h30))

def paired_preimage_exists : KDerivation (imp sourceMatrix.encode (imp firstBijection.encode
    (imp (member 42 33) (existsCode 32 (existsCode 30 (existsCode 31 pairedBody.encode)))))) := by
  have hlift := conditionalExistsCongr 32 (guard.vacuity 32 (by decide)) coordinates_retained
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 42 33,firstBijection.encode,sourceMatrix.encode]
  have hy : Context Γ (member 42 33) := .head _ _
  have hb : Context Γ firstBijection.encode := .hypothesis (by simp [Γ])
  have hm : Context Γ sourceMatrix.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ guard.encode := by
    simpa [guard, namedBoth, Formula.not, Formula.encode, both, neg] using Context.conjunctionIntro hm hb
  have hw := Context.mp hy (Context.mp hb (.closed output_preimage))
  simpa [Γ] using Context.mp hw (Context.mp hg (.closed hlift))

theorem paired_preimage_exists_certificate : theoremCode (certificate paired_preimage_exists) =
    imp sourceMatrix.encode (imp firstBijection.encode (imp (member 42 33)
      (existsCode 32 (existsCode 30 (existsCode 31 pairedBody.encode))))) := certificate_correct _

end PASoundness.PAtoCompactProductOutputPreimagePoint

#print axioms PASoundness.PAtoCompactProductOutputPreimagePoint.source_coordinates
#print axioms PASoundness.PAtoCompactProductOutputPreimagePoint.output_preimage
#print axioms PASoundness.PAtoCompactProductOutputPreimagePoint.coordinates_retained
#print axioms PASoundness.PAtoCompactProductOutputPreimagePoint.paired_preimage_exists
#print axioms PASoundness.PAtoCompactProductOutputPreimagePoint.paired_preimage_exists_certificate
