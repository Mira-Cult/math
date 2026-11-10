import PASoundness.PAtoCompactFirstSuffixInverseSelected
import PASoundness.PAtoCompactConditionalTransitivityFirstUnique
import PASoundness.PAtoCompactFirstSpanTargetOutside

/-! Derive the second-graph selected forward-uniqueness test from an actual
common-source-to-suffix bijection and stored-pair cleanliness. The two whole
target-membership antecedents in the test remain explicit, even though suffix
memberships are obtained from the actual clean graph edges. -/
namespace PASoundness.PAtoCompactSecondSuffixForwardSelected

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactConditionalTransitivityFirstUnique PASoundness.PAtoCompactConditionalTransitivityUniqueness
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactSuffixCleanGraphGuard PASoundness.PAtoCompactFirstSpanTargetOutside
open PASoundness.PAtoCompactSeededSpanSelectedPathUniqueness

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def suffixBijection : Formula := replace 6 7
  (replace 25 1 (replace 1 38 (replace 0 25 bijectionFormula)))
private def localBody : Formula := .imp (.member 0 2) (.imp (.member 1 10)
  (.imp (.member 1 11) (.imp (graphFormula 6 2 10)
    (.imp (graphFormula 6 2 11) (.equal 10 11)))))
private def frame : Formula := .imp bijectionFormula (.imp (.member 0 2) localBody)
private def f25 : Formula := replace 0 25 frame
private def f38 : Formula := replace 1 38 f25
private def f1 : Formula := replace 25 1 f38
private def suffixLocal : Formula := replace 6 7
  (replace 25 1 (replace 1 38 (replace 0 25 localBody)))
private def point : Formula := .imp (.member 1 2) suffixLocal
private def p42 : Formula := replace 2 42 point
private def p3 : Formula := replace 10 3 p42
private def p27 : Formula := replace 11 27 p3
private theorem p27_alignment : p27 = .imp (.member 1 42) (.imp (.member 1 42)
  (.imp (.member 38 3) (.imp (.member 38 27) (.imp (graphFormula 7 42 3)
    (.imp (graphFormula 7 42 27) (.equal 3 27)))))) := by decide

private def forward_from_suffix : KDerivation (imp suffixBijection.encode point.encode) := by
  have hbase : KDerivation frame.encode := by
    simpa only [frame,localBody,firstUnique,Formula.encode] using first_unique_of_bijection
  have h25 := replace_derivation 0 25 frame (by decide) (by decide) hbase
  have h38 := replace_derivation 1 38 f25 (by decide) (by decide) (by simpa only [f25] using h25)
  have h1 := replace_derivation 25 1 f38 (by decide) (by decide) (by simpa only [f38] using h38)
  have h7 := replace_derivation 6 7 f1 (by decide) (by decide) (by simpa only [f1] using h1)
  have ha : replace 6 7 f1 = .imp suffixBijection point := by decide
  rw [ha] at h7
  exact h7

private def forward_at_points : KDerivation (imp suffixBijection.encode p27.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [suffixBijection.encode]
  have hb : Context Γ suffixBijection.encode := .head _ _
  have hlocal : Context Γ point.encode := .mp hb (.closed forward_from_suffix)
  have hv (v : Nat) (fresh : v ∉ suffixBijection.free) :
      ∀ h, h ∈ Γ → KDerivation (imp h (allCode v h)) := by
    intro h hh
    have he : h = suffixBijection.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity v suffixBijection fresh
  have hall : Context Γ (allCode 2 (allCode 10 (allCode 11 point.encode))) :=
    Context.generalize 2 (hv 2 (by decide))
      (Context.generalize 10 (hv 10 (by decide)) (Context.generalize 11 (hv 11 (by decide)) hlocal))
  have h2 := universalInstance 2 42 (.all 10 (.all 11 point)) (by decide) (by decide) (by decide)
  have ha2 : replace 2 42 (.all 10 (.all 11 point)) = .all 10 (.all 11 p42) := by decide
  rw [ha2] at h2
  have h10 := universalInstance 10 3 (.all 11 p42) (by decide) (by decide) (by decide)
  have ha10 : replace 10 3 (.all 11 p42) = .all 11 p3 := by decide
  rw [ha10] at h10
  have h11 := universalInstance 11 27 p3 (by decide) (by decide) (by decide)
  have ha11 : replace 11 27 p3 = p27 := by rfl
  rw [ha11] at h11
  exact .mp (.mp (.mp hall (.closed h2)) (.closed h10)) (.closed h11)

private def cleanFrame : Formula := .imp storedClean (.imp (graphFormula 6 2 4) (.member 31 4))
private def c42 : Formula := replace 2 42 cleanFrame
private def c3 : Formula := replace 4 3 c42
private def c27 : Formula := replace 4 27 c42
private def c338 : Formula := replace 31 38 c3
private def c2738 : Formula := replace 31 38 c27

private def clean_at_three : KDerivation
    (imp targetClean.encode (imp (graphFormula 7 42 3).encode (member 38 3))) := by
  have hbase : KDerivation cleanFrame.encode := by simpa only [cleanFrame,Formula.encode] using clean_target_point
  have h42 := replace_derivation 2 42 cleanFrame (by decide) (by decide) hbase
  have h3 := replace_derivation 4 3 c42 (by decide) (by decide) (by simpa only [c42] using h42)
  have h38 := replace_derivation 31 38 c3 (by decide) (by decide) (by simpa only [c3] using h3)
  have h7 := replace_derivation 6 7 c338 (by decide) (by decide) (by simpa only [c338] using h38)
  have ha : replace 6 7 c338 = .imp targetClean (.imp (graphFormula 7 42 3) (.member 38 3)) := by decide
  rw [ha] at h7
  exact h7

private def clean_at_twentyseven : KDerivation
    (imp targetClean.encode (imp (graphFormula 7 42 27).encode (member 38 27))) := by
  have hbase : KDerivation cleanFrame.encode := by simpa only [cleanFrame,Formula.encode] using clean_target_point
  have h42 := replace_derivation 2 42 cleanFrame (by decide) (by decide) hbase
  have h27 := replace_derivation 4 27 c42 (by decide) (by decide) (by simpa only [c42] using h42)
  have h38 := replace_derivation 31 38 c27 (by decide) (by decide) (by simpa only [c27] using h27)
  have h7 := replace_derivation 6 7 c2738 (by decide) (by decide) (by simpa only [c2738] using h38)
  have ha : replace 6 7 c2738 = .imp targetClean (.imp (graphFormula 7 42 27) (.member 38 27)) := by decide
  rw [ha] at h7
  exact h7

/-- The selected forward test follows from the actual suffix bijection and
both corresponding edges of the supplied clean graph. -/
def selected_second_forward : KDerivation (imp suffixBijection.encode
    (imp targetClean.encode secondForward)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 7 42 27).encode,(graphFormula 7 42 3).encode,member 8 27,
    member 8 3,member 1 42,targetClean.encode,suffixBijection.encode]
  have he2 : Context Γ (graphFormula 7 42 27).encode := .head _ _
  have he1 : Context Γ (graphFormula 7 42 3).encode := .hypothesis (by simp [Γ])
  have hsource : Context Γ (member 1 42) := .hypothesis (by simp [Γ])
  have hc : Context Γ targetClean.encode := .hypothesis (by simp [Γ])
  have hb : Context Γ suffixBijection.encode := .hypothesis (by simp [Γ])
  have hm3 : Context Γ (member 38 3) := .mp he1 (.mp hc (.closed clean_at_three))
  have hm27 : Context Γ (member 38 27) := .mp he2 (.mp hc (.closed clean_at_twentyseven))
  have hl : Context Γ p27.encode := .mp hb (.closed forward_at_points)
  have hgoal : Context Γ (imp (member 1 42) (imp (member 1 42) (imp (member 38 3)
    (imp (member 38 27) (imp (graphFormula 7 42 3).encode
      (imp (graphFormula 7 42 27).encode (equal 3 27))))))) := by
    simpa only [p27_alignment,Formula.encode] using hl
  exact .mp he2 (.mp he1 (.mp hm27 (.mp hm3 (.mp hsource (.mp hsource hgoal)))))

theorem selected_second_forward_certificate : theoremCode (certificate selected_second_forward) =
    imp suffixBijection.encode (imp targetClean.encode secondForward) := certificate_correct selected_second_forward

end PASoundness.PAtoCompactSecondSuffixForwardSelected

#print axioms PASoundness.PAtoCompactSecondSuffixForwardSelected.suffixBijection
#print axioms PASoundness.PAtoCompactSecondSuffixForwardSelected.selected_second_forward
#print axioms PASoundness.PAtoCompactSecondSuffixForwardSelected.selected_second_forward_certificate
