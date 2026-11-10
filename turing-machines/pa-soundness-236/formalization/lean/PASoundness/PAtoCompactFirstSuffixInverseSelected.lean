import PASoundness.PAtoCompactSeededSpanSelectedPathUniqueness
import PASoundness.PAtoCompactConditionalTransitivityFirstInverse
import PASoundness.PAtoCompactSuffixCleanGraphGuard
import PASoundness.PAtoCompactScopedActiveReplace
import PASoundness.PAtoCompactFreeVacuity

/-! Derive the first-graph selected inverse-uniqueness test from the actual
common-source-to-suffix bijection and its stored-pair cleanliness. The
bijection and clean graph remain explicit K antecedents. -/
namespace PASoundness.PAtoCompactFirstSuffixInverseSelected

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactConditionalTransitivityFirstInverse PASoundness.PAtoCompactConditionalTransitivityUniqueness
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactSuffixCleanGraphGuard PASoundness.PAtoCompactSeededSpanSelectedPathUniqueness

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def suffixBijection : Formula := replace 25 1 (replace 1 31 (replace 0 25 bijectionFormula))
private def localBody : Formula := .imp (.member 1 10) (.imp (.member 0 2)
  (.imp (.member 0 4) (.imp (graphFormula 6 2 10)
    (.imp (graphFormula 6 4 10) (.equal 2 4)))))
private def frame : Formula := .imp bijectionFormula (.imp (.member 1 10) localBody)
private def f25 : Formula := replace 0 25 frame
private def f31 : Formula := replace 1 31 f25
private def suffixLocal : Formula := replace 25 1 (replace 1 31 (replace 0 25 localBody))
private def point : Formula := .imp (.member 31 10) suffixLocal
private def p42 : Formula := replace 2 42 point
private def p43 : Formula := replace 4 43 p42
private def p2 : Formula := replace 10 2 p43
private theorem p2_alignment : p2 = .imp (.member 31 2) (.imp (.member 31 2)
  (.imp (.member 1 42) (.imp (.member 1 43) (.imp (graphFormula 6 42 2)
    (.imp (graphFormula 6 43 2) (.equal 42 43)))))) := by decide

private def inverse_from_suffix : KDerivation (imp suffixBijection.encode point.encode) := by
  have hbase : KDerivation frame.encode := by
    simpa only [frame,localBody,firstInverseUnique,Formula.encode] using first_inverse_unique_of_bijection
  have h25 := replace_derivation 0 25 frame (by decide) (by decide) hbase
  have h31 := replace_derivation 1 31 f25 (by decide) (by decide) (by simpa only [f25] using h25)
  have h1 := replace_derivation 25 1 f31 (by decide) (by decide) (by simpa only [f31] using h31)
  have ha : replace 25 1 f31 = .imp suffixBijection point := by decide
  rw [ha] at h1
  exact h1

private def inverse_at_points : KDerivation (imp suffixBijection.encode p2.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [suffixBijection.encode]
  have hb : Context Γ suffixBijection.encode := .head _ _
  have hlocal : Context Γ point.encode := .mp hb (.closed inverse_from_suffix)
  have hv (v : Nat) (fresh : v ∉ suffixBijection.free) :
      ∀ h, h ∈ Γ → KDerivation (imp h (allCode v h)) := by
    intro h hh
    have he : h = suffixBijection.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity v suffixBijection fresh
  have hall : Context Γ (allCode 2 (allCode 4 (allCode 10 point.encode))) :=
    Context.generalize 2 (hv 2 (by decide))
      (Context.generalize 4 (hv 4 (by decide)) (Context.generalize 10 (hv 10 (by decide)) hlocal))
  have h2 := universalInstance 2 42 (.all 4 (.all 10 point)) (by decide) (by decide) (by decide)
  have ha2 : replace 2 42 (.all 4 (.all 10 point)) = .all 4 (.all 10 p42) := by decide
  rw [ha2] at h2
  have h4 := universalInstance 4 43 (.all 10 p42) (by decide) (by decide) (by decide)
  have ha4 : replace 4 43 (.all 10 p42) = .all 10 p43 := by decide
  rw [ha4] at h4
  have h10 := universalInstance 10 2 p43 (by decide) (by decide) (by decide)
  have ha10 : replace 10 2 p43 = p2 := by rfl
  rw [ha10] at h10
  exact .mp (.mp (.mp hall (.closed h2)) (.closed h4)) (.closed h10)

private def cleanFrame : Formula := .imp storedClean (.imp (graphFormula 6 2 4) (.member 31 4))
private def clean42 : Formula := replace 2 42 cleanFrame
private def clean_at_points : KDerivation
    (imp storedClean.encode (imp (graphFormula 6 42 2).encode (member 31 2))) := by
  have hbase : KDerivation cleanFrame.encode := by simpa only [cleanFrame,Formula.encode] using clean_target_point
  have h42 := replace_derivation 2 42 cleanFrame (by decide) (by decide) hbase
  have h2 := replace_derivation 4 2 clean42 (by decide) (by decide) (by simpa only [clean42] using h42)
  have ha : replace 4 2 clean42 = .imp storedClean (.imp (graphFormula 6 42 2) (.member 31 2)) := by decide
  rw [ha] at h2
  exact h2

/-- The selected inverse test follows from the literal suffix bijection and
the actual clean graph. Its original whole-membership antecedent is retained. -/
def selected_first_inverse : KDerivation (imp suffixBijection.encode
    (imp storedClean.encode firstInverse)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 6 43 2).encode,(graphFormula 6 42 2).encode,member 1 43,
    member 1 42,member 0 2,storedClean.encode,suffixBijection.encode]
  have he2 : Context Γ (graphFormula 6 43 2).encode := .head _ _
  have he1 : Context Γ (graphFormula 6 42 2).encode := .hypothesis (by simp [Γ])
  have hm43 : Context Γ (member 1 43) := .hypothesis (by simp [Γ])
  have hm42 : Context Γ (member 1 42) := .hypothesis (by simp [Γ])
  have hc : Context Γ storedClean.encode := .hypothesis (by simp [Γ])
  have hb : Context Γ suffixBijection.encode := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 31 2) := .mp he1 (.mp hc (.closed clean_at_points))
  have hl : Context Γ p2.encode := .mp hb (.closed inverse_at_points)
  have hgoal : Context Γ (imp (member 31 2) (imp (member 31 2) (imp (member 1 42)
    (imp (member 1 43) (imp (graphFormula 6 42 2).encode
      (imp (graphFormula 6 43 2).encode (equal 42 43))))))) := by
    simpa only [p2_alignment,Formula.encode] using hl
  exact .mp he2 (.mp he1 (.mp hm43 (.mp hm42 (.mp hm (.mp hm hgoal)))))

theorem selected_first_inverse_certificate : theoremCode (certificate selected_first_inverse) =
    imp suffixBijection.encode (imp storedClean.encode firstInverse) := certificate_correct selected_first_inverse

end PASoundness.PAtoCompactFirstSuffixInverseSelected

#print axioms PASoundness.PAtoCompactFirstSuffixInverseSelected.suffixBijection
#print axioms PASoundness.PAtoCompactFirstSuffixInverseSelected.selected_first_inverse
#print axioms PASoundness.PAtoCompactFirstSuffixInverseSelected.selected_first_inverse_certificate
