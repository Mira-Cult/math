import PASoundness.PAtoCompactFirstSuffixPreimage
import PASoundness.PAtoCompactSecondSuffixForwardSelected

/-! The second suffix bijection provides a common-source preimage of an actual
suffix38 point. The specified target point is instantiated under the fixed
bijection context, preserving the existential witness and graph edge. -/
namespace PASoundness.PAtoCompactSecondSuffixPreimage

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactFreeVacuity

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def suffixBijection : Formula := PASoundness.PAtoCompactSecondSuffixForwardSelected.suffixBijection
private def firstBijection : Formula := PASoundness.PAtoCompactFirstSuffixInverseSelected.suffixBijection
private def frame : Formula := .imp firstBijection (.imp (.member 31 2)
  PASoundness.PAtoCompactFirstSuffixPreimage.preimage)
private def f38 : Formula := replace 31 38 frame
private def body2 : Formula := namedBoth (.member 1 42) (graphFormula 7 42 2)
private def point : Formula := .imp (.member 38 2) (.ex 42 body2)
def preimageBody : Formula := namedBoth (.member 1 42) (graphFormula 7 42 3)
def preimage : Formula := .ex 42 preimageBody
private theorem frame_alignment : replace 6 7 f38 = .imp suffixBijection point := by decide
private theorem point_alignment : replace 2 3 point = .imp (.member 38 3) preimage := by decide

private def raw_preimage : KDerivation (imp suffixBijection.encode point.encode) := by
  have hbase : KDerivation frame.encode := by
    simpa only [frame,firstBijection,Formula.encode] using PASoundness.PAtoCompactFirstSuffixPreimage.first_suffix_preimage
  have h38 := replace_derivation 31 38 frame (by decide) (by decide) hbase
  have h7 := replace_derivation 6 7 f38 (by decide) (by decide) (by simpa only [f38] using h38)
  rw [frame_alignment] at h7
  exact h7

/-- The preimage and its graph7 edge use the same common-source witness42. -/
def second_suffix_preimage : KDerivation (imp suffixBijection.encode
    (imp (member 38 3) preimage.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [suffixBijection.encode]
  have hb : Context Γ suffixBijection.encode := .head _ _
  have hp : Context Γ point.encode := .mp hb (.closed raw_preimage)
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 2 h)) := by
    intro h hh
    have he : h = suffixBijection.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 2 suffixBijection (by decide)
  have hall : Context Γ (allCode 2 point.encode) := Context.generalize 2 hv hp
  have hi := universalInstance 2 3 point (by decide) (by decide) (by decide)
  rw [point_alignment] at hi
  exact .mp hall (.closed hi)

theorem second_suffix_preimage_certificate : theoremCode (certificate second_suffix_preimage) =
    imp suffixBijection.encode (imp (member 38 3) preimage.encode) := certificate_correct second_suffix_preimage

end PASoundness.PAtoCompactSecondSuffixPreimage

#print axioms PASoundness.PAtoCompactSecondSuffixPreimage.suffixBijection
#print axioms PASoundness.PAtoCompactSecondSuffixPreimage.preimageBody
#print axioms PASoundness.PAtoCompactSecondSuffixPreimage.preimage
#print axioms PASoundness.PAtoCompactSecondSuffixPreimage.second_suffix_preimage
#print axioms PASoundness.PAtoCompactSecondSuffixPreimage.second_suffix_preimage_certificate
