import PASoundness.PAtoCompactSecondSuffixForwardSelected

/-! Derive the second selected inverse-uniqueness test by capture-safe K
renaming of the first-suffix inverse theorem. The target point is generalized
only under the fixed bijection and clean-graph contexts before instantiation. -/
namespace PASoundness.PAtoCompactSecondSuffixInverseSelected

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactSuffixCleanGraphGuard
open PASoundness.PAtoCompactFirstSpanTargetOutside PASoundness.PAtoCompactSeededSpanSelectedPathUniqueness

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def firstBijection : Formula := PASoundness.PAtoCompactFirstSuffixInverseSelected.suffixBijection
def secondBijection : Formula := PASoundness.PAtoCompactSecondSuffixForwardSelected.suffixBijection
private def firstPoint : Formula := .imp (.member 0 2) (.imp (.member 1 42) (.imp (.member 1 43)
  (.imp (graphFormula 6 42 2) (.imp (graphFormula 6 43 2) (.equal 42 43)))))
private def frame : Formula := .imp firstBijection (.imp storedClean firstPoint)
private def p38 : Formula := replace 31 38 frame
private def p7 : Formula := replace 6 7 p38
private def point : Formula := .imp (.member 8 2) (.imp (.member 1 42) (.imp (.member 1 43)
  (.imp (graphFormula 7 42 2) (.imp (graphFormula 7 43 2) (.equal 42 43)))))
private theorem frame_alignment : replace 0 8 p7 = .imp secondBijection (.imp targetClean point) := by decide
private theorem point_alignment : replace 2 3 point = .imp (.member 8 3)
  (.imp (.member 1 42) (.imp (.member 1 43) (.imp (graphFormula 7 42 3)
    (.imp (graphFormula 7 43 3) (.equal 42 43))))) := by decide

private def renamed : KDerivation (imp secondBijection.encode (imp targetClean.encode point.encode)) := by
  have hbase : KDerivation frame.encode := by
    simpa only [frame,firstBijection,firstPoint,firstInverse,Formula.encode] using
      PASoundness.PAtoCompactFirstSuffixInverseSelected.selected_first_inverse
  have h38 := replace_derivation 31 38 frame (by decide) (by decide) hbase
  have h7 := replace_derivation 6 7 p38 (by decide) (by decide) (by simpa only [p38] using h38)
  have h8 := replace_derivation 0 8 p7 (by decide) (by decide) (by simpa only [p7] using h7)
  rw [frame_alignment] at h8
  exact h8

/-- The actual suffix38 bijection and stored-clean graph7 supply the selected
inverse uniqueness test, with target membership guarded in the test. -/
def selected_second_inverse : KDerivation (imp secondBijection.encode
    (imp targetClean.encode secondInverse)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [targetClean.encode,secondBijection.encode]
  have hc : Context Γ targetClean.encode := .head _ _
  have hb : Context Γ secondBijection.encode := .hypothesis (by simp [Γ])
  have hp : Context Γ point.encode := .mp hc (.mp hb (.closed renamed))
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 2 h)) := by
    intro h hh
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases he : h = targetClean.encode
    · subst h; exact free_vacuity 2 targetClean (by decide)
    · have he' : h = secondBijection.encode := hh.resolve_left he
      subst h; exact free_vacuity 2 secondBijection (by decide)
  have hall : Context Γ (allCode 2 point.encode) := Context.generalize 2 hv hp
  have hi := universalInstance 2 3 point (by decide) (by decide) (by decide)
  rw [point_alignment] at hi
  have hpoint : Context Γ (imp (member 8 3) (imp (member 1 42) (imp (member 1 43)
      (imp (graphFormula 7 42 3).encode (imp (graphFormula 7 43 3).encode (equal 42 43)))))) :=
    .mp hall (.closed hi)
  exact hpoint

theorem selected_second_inverse_certificate : theoremCode (certificate selected_second_inverse) =
    imp secondBijection.encode (imp targetClean.encode secondInverse) := certificate_correct selected_second_inverse

end PASoundness.PAtoCompactSecondSuffixInverseSelected

#print axioms PASoundness.PAtoCompactSecondSuffixInverseSelected.secondBijection
#print axioms PASoundness.PAtoCompactSecondSuffixInverseSelected.selected_second_inverse
#print axioms PASoundness.PAtoCompactSecondSuffixInverseSelected.selected_second_inverse_certificate
