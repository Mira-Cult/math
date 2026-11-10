import PASoundness.PAtoCompactSecondSuffixForwardSelected
import PASoundness.PAtoCompactTransitiveWitness

/-! A supplied source1→suffix38 graph7 bijection gives an actual suffix image
of a specified common-source point 42. The same target witness is retained
in its suffix membership and graph edge. -/
namespace PASoundness.PAtoCompactSecondSuffixImage

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactTransitiveWitness
open PASoundness.PAtoCompactSecondSuffixForwardSelected

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def sourceWitness : Formula := namedBoth (.member 38 3) (namedBoth (graphFormula 7 2 3)
  (.all 4 (.imp (namedBoth (.member 38 4) (graphFormula 7 2 4)) (.equal 4 3))))
private def sourceBody : Formula := .imp (.member 1 2) (.ex 3 sourceWitness)
private def sourceForward : Formula := .all 2 sourceBody
private def witness42 : Formula := replace 2 42 sourceWitness
def imageBody : Formula := namedBoth (.member 38 3) (graphFormula 7 42 3)
def image : Formula := .ex 3 imageBody

/-- The same image witness has both the literal suffix membership and edge. -/
def second_suffix_image : KDerivation (imp suffixBijection.encode
    (imp (member 1 42) image.encode)) := by
  have hi := universalInstance 2 42 sourceBody (by decide) (by decide) (by decide)
  have ha : replace 2 42 sourceBody = .imp (.member 1 42) (.ex 3 witness42) := by decide
  rw [ha] at hi
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 1 42,suffixBijection.encode]
  have hm : Context Γ (member 1 42) := .head _ _
  have hb : Context Γ suffixBijection.encode := .hypothesis (by simp [Γ])
  have hf : Context Γ sourceForward.encode := by
    change Context Γ (both sourceForward.encode _) at hb
    exact Context.conjunctionLeft hb
  have hex : Context Γ (existsCode 3 witness42.encode) := .mp hm (.mp hf (.closed hi))
  have hlocal : Context Γ (imp witness42.encode imageBody.encode) := by
    apply Context.deduction
    let Δ := [witness42.encode,member 1 42,suffixBijection.encode]
    have hw : Context Δ witness42.encode := .head _ _
    have hm' : Context Δ (member 38 3) := Context.conjunctionLeft hw
    have he : Context Δ (graphFormula 7 42 3).encode := Context.conjunctionLeft (Context.conjunctionRight hw)
    exact Context.conjunctionIntro hm' he
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 3 h)) := by
    intro h hh
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases he : h = member 1 42
    · subst h; exact free_vacuity 3 (.member 1 42) (by decide)
    · have he' : h = suffixBijection.encode := hh.resolve_left he
      subst h; exact free_vacuity 3 suffixBijection (by decide)
  have hall := Context.generalize 3 hv hlocal
  simpa only [image,Formula.encode] using exists_map_context hall hex

theorem second_suffix_image_certificate : theoremCode (certificate second_suffix_image) =
    imp suffixBijection.encode (imp (member 1 42) image.encode) := certificate_correct second_suffix_image

end PASoundness.PAtoCompactSecondSuffixImage

#print axioms PASoundness.PAtoCompactSecondSuffixImage.imageBody
#print axioms PASoundness.PAtoCompactSecondSuffixImage.image
#print axioms PASoundness.PAtoCompactSecondSuffixImage.second_suffix_image
#print axioms PASoundness.PAtoCompactSecondSuffixImage.second_suffix_image_certificate
