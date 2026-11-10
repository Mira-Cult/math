import PASoundness.PAtoCompactFirstSuffixInverseSelected
import PASoundness.PAtoCompactConditionalTransitivityReverseExtract

/-! A supplied source1→suffix31 bijection gives an actual common-source
preimage of a specified suffix point 2. The existential source binder is
alpha-renamed before the target point is instantiated, preserving the same
graph edge and avoiding capture. -/
namespace PASoundness.PAtoCompactFirstSuffixPreimage

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactFirstSuffixInverseSelected

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def rawBody : Formula := namedBoth (.member 0 2) (graphFormula 6 2 10)
private def frame : Formula := .imp bijectionFormula (.imp (.member 1 10) (.ex 2 rawBody))
private def f25 : Formula := replace 0 25 frame
private def f31 : Formula := replace 1 31 f25
private def body : Formula := namedBoth (.member 1 2) (graphFormula 6 2 10)
private def movedBody : Formula := replace 2 42 body
private def point : Formula := .imp (.member 31 10) (.ex 42 movedBody)
def preimageBody : Formula := namedBoth (.member 1 42) (graphFormula 6 42 2)
def preimage : Formula := .ex 42 preimageBody

private def raw_preimage : KDerivation (imp suffixBijection.encode
    (imp (member 31 10) (existsCode 2 body.encode))) := by
  have hbase : KDerivation frame.encode := by
    simpa only [frame,rawBody,namedBoth,Formula.encode,CompactProof.both,CompactProof.neg] using
      PASoundness.PAtoCompactConditionalTransitivityReverseExtract.f_preimage
  have h25 := replace_derivation 0 25 frame (by decide) (by decide) hbase
  have h31 := replace_derivation 1 31 f25 (by decide) (by decide) (by simpa only [f25] using h25)
  have h1 := replace_derivation 25 1 f31 (by decide) (by decide) (by simpa only [f31] using h31)
  have ha : replace 25 1 f31 = .imp suffixBijection (.imp (.member 31 10) (.ex 2 body)) := by decide
  rw [ha] at h1
  exact h1

/-- The same literal graph6 edge and its common-source witness are retained. -/
def first_suffix_preimage : KDerivation (imp suffixBijection.encode
    (imp (member 31 2) preimage.encode)) := by
  have halpha := (existentialAlpha 2 42 body (by decide) (by decide) (by decide)).1
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [suffixBijection.encode]
  have hb : Context Γ suffixBijection.encode := .head _ _
  have hpoint : Context Γ point.encode := by
    apply Context.deduction
    let Δ := [member 31 10,suffixBijection.encode]
    have hm : Context Δ (member 31 10) := .head _ _
    have hb' : Context Δ suffixBijection.encode := .under hb (member 31 10)
    have he : Context Δ (existsCode 2 body.encode) := .mp hm (.mp hb' (.closed raw_preimage))
    exact .mp he (.closed halpha)
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 10 h)) := by
    intro h hh
    have he : h = suffixBijection.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 10 suffixBijection (by decide)
  have hall : Context Γ (allCode 10 point.encode) := Context.generalize 10 hv hpoint
  have hi := universalInstance 10 2 point (by decide) (by decide) (by decide)
  have ha : replace 10 2 point = .imp (.member 31 2) preimage := by decide
  rw [ha] at hi
  exact .mp hall (.closed hi)

theorem first_suffix_preimage_certificate : theoremCode (certificate first_suffix_preimage) =
    imp suffixBijection.encode (imp (member 31 2) preimage.encode) := certificate_correct first_suffix_preimage

end PASoundness.PAtoCompactFirstSuffixPreimage

#print axioms PASoundness.PAtoCompactFirstSuffixPreimage.preimageBody
#print axioms PASoundness.PAtoCompactFirstSuffixPreimage.preimage
#print axioms PASoundness.PAtoCompactFirstSuffixPreimage.first_suffix_preimage
#print axioms PASoundness.PAtoCompactFirstSuffixPreimage.first_suffix_preimage_certificate
