import PASoundness.PAtoCompactSecondSuffixForwardSelected

/-! Derive the first selected forward-uniqueness test by capture-safe K
renaming of the second-suffix forward theorem. Point names 3 and 27 are
generalized only under fixed bijection and clean-graph contexts. -/
namespace PASoundness.PAtoCompactFirstSuffixForwardSelected

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactSuffixCleanGraphGuard
open PASoundness.PAtoCompactFirstSpanTargetOutside PASoundness.PAtoCompactSeededSpanSelectedPathUniqueness

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def firstBijection : Formula := PASoundness.PAtoCompactFirstSuffixInverseSelected.suffixBijection
private def secondBijection : Formula := PASoundness.PAtoCompactSecondSuffixForwardSelected.suffixBijection
private def secondPoint : Formula := .imp (.member 1 42) (.imp (.member 8 3) (.imp (.member 8 27)
  (.imp (graphFormula 7 42 3) (.imp (graphFormula 7 42 27) (.equal 3 27)))))
private def frame : Formula := .imp secondBijection (.imp targetClean secondPoint)
private def p31 : Formula := replace 38 31 frame
private def p6 : Formula := replace 7 6 p31
private def point : Formula := .imp (.member 1 42) (.imp (.member 0 3) (.imp (.member 0 27)
  (.imp (graphFormula 6 42 3) (.imp (graphFormula 6 42 27) (.equal 3 27)))))
private def at2 : Formula := replace 3 2 point
private def at26 : Formula := replace 27 26 at2
private theorem frame_alignment : replace 8 0 p6 = .imp firstBijection (.imp storedClean point) := by decide
private theorem point_alignment : at26 = .imp (.member 1 42) (.imp (.member 0 2)
  (.imp (.member 0 26) (.imp (graphFormula 6 42 2)
    (.imp (graphFormula 6 42 26) (.equal 2 26))))) := by decide

private def renamed : KDerivation (imp firstBijection.encode (imp storedClean.encode point.encode)) := by
  have hbase : KDerivation frame.encode := by
    simpa only [frame,secondBijection,secondPoint,secondForward,Formula.encode] using
      PASoundness.PAtoCompactSecondSuffixForwardSelected.selected_second_forward
  have h31 := replace_derivation 38 31 frame (by decide) (by decide) hbase
  have h6 := replace_derivation 7 6 p31 (by decide) (by decide) (by simpa only [p31] using h31)
  have h0 := replace_derivation 8 0 p6 (by decide) (by decide) (by simpa only [p6] using h6)
  rw [frame_alignment] at h0
  exact h0

/-- The actual suffix31 bijection and stored-clean graph6 supply the selected
forward uniqueness test, retaining both whole-membership antecedents. -/
def selected_first_forward : KDerivation (imp firstBijection.encode
    (imp storedClean.encode firstForward)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [storedClean.encode,firstBijection.encode]
  have hc : Context Γ storedClean.encode := .head _ _
  have hb : Context Γ firstBijection.encode := .hypothesis (by simp [Γ])
  have hp : Context Γ point.encode := .mp hc (.mp hb (.closed renamed))
  have hv (v : Nat) (freshC : v ∉ storedClean.free) (freshB : v ∉ firstBijection.free) :
      ∀ h, h ∈ Γ → KDerivation (imp h (allCode v h)) := by
    intro h hh
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases he : h = storedClean.encode
    · subst h; exact free_vacuity v storedClean freshC
    · have he' : h = firstBijection.encode := hh.resolve_left he
      subst h; exact free_vacuity v firstBijection freshB
  have hall : Context Γ (allCode 3 (allCode 27 point.encode)) :=
    Context.generalize 3 (hv 3 (by decide) (by decide))
      (Context.generalize 27 (hv 27 (by decide) (by decide)) hp)
  have h3 := universalInstance 3 2 (.all 27 point) (by decide) (by decide) (by decide)
  have ha3 : replace 3 2 (.all 27 point) = .all 27 at2 := by decide
  rw [ha3] at h3
  have h27 := universalInstance 27 26 at2 (by decide) (by decide) (by decide)
  have ha27 : replace 27 26 at2 = at26 := by rfl
  rw [ha27] at h27
  have hpoint : Context Γ at26.encode := .mp (.mp hall (.closed h3)) (.closed h27)
  simpa only [Γ,point_alignment,Formula.encode,firstForward] using hpoint

theorem selected_first_forward_certificate : theoremCode (certificate selected_first_forward) =
    imp firstBijection.encode (imp storedClean.encode firstForward) := certificate_correct selected_first_forward

end PASoundness.PAtoCompactFirstSuffixForwardSelected

#print axioms PASoundness.PAtoCompactFirstSuffixForwardSelected.firstBijection
#print axioms PASoundness.PAtoCompactFirstSuffixForwardSelected.selected_first_forward
#print axioms PASoundness.PAtoCompactFirstSuffixForwardSelected.selected_first_forward_certificate
