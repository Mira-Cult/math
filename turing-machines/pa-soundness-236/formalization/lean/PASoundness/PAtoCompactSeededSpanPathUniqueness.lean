import PASoundness.PAtoCompactSelectedPathUniquenessFromBijections
import PASoundness.PAtoCompactSeededSpanOrderSplit
import PASoundness.PAtoCompactSuccGraphOutputLift
import PASoundness.PAtoCompactFreeVacuity

/-! Derive both path/path pointwise uniqueness branches from the actual two
suffix bijections, stored-clean graphs and whole endpoint memberships. Both
actual path witnesses are alpha-renamed and eliminated inside K. -/
namespace PASoundness.PAtoCompactSeededSpanPathUniqueness

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactCommonSourceSpanBase PASoundness.PAtoCompactSeededSpanOrderSplit
open PASoundness.PAtoCompactSeededSpanOrderCases PASoundness.PAtoCompactSeededSpanPointUniqueness
open PASoundness.PAtoCompactSeededSpanSelectedPathUniqueness PASoundness.PAtoCompactSelectedPathUniquenessFromBijections
open PASoundness.PAtoCompactSuffixCleanGraphGuard PASoundness.PAtoCompactFirstSpanTargetOutside
open PASoundness.PAtoCompactSuccGraphOutputLift

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def pathGuard : Formula := namedBoth firstBijection (namedBoth storedClean
  (namedBoth secondBijection (namedBoth targetClean (namedBoth (.member 0 2)
    (namedBoth (.member 0 26) (namedBoth (.member 8 3) (.member 8 27)))))))
private def firstBody : Formula := replace 4 42 spanPathBody
private def secondBody : Formula := replace 4 43 (replace 3 27 (replace 2 26 spanPathBody))
private def firstExists : Formula := .ex 42 firstBody
private def secondExists : Formula := .ex 43 secondBody
private def pointEq : Formula := namedBoth (.imp (.equal 2 26) (.equal 3 27))
  (.imp (.equal 3 27) (.equal 2 26))
private theorem point_eq_code : pointEq.encode = pointUniqueness := by rfl
private theorem moved_path_shape : movedPath =
    .ex 4 (replace 3 27 (replace 2 26 spanPathBody)) := by decide

private def selected : KDerivation (imp pathGuard.encode
    (imp firstBody.encode (imp secondBody.encode pointUniqueness))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [secondBody.encode,firstBody.encode,pathGuard.encode]
  have hb2 : Context Γ secondBody.encode := .head _ _
  have hb1 : Context Γ firstBody.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ pathGuard.encode := .hypothesis (by simp [Γ])
  have hfirst : Context Γ firstBijection.encode := Context.conjunctionLeft hg
  have hr := Context.conjunctionRight hg
  have hclean1 : Context Γ storedClean.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hsecond : Context Γ secondBijection.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hclean2 : Context Γ targetClean.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hm02 : Context Γ (member 0 2) := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hm026 : Context Γ (member 0 26) := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hm83 : Context Γ (member 8 3) := Context.conjunctionLeft hr
  have hm827 : Context Γ (member 8 27) := Context.conjunctionRight hr
  have hs42 : Context Γ (member 1 42) := Context.conjunctionLeft hb1
  have hs43 : Context Γ (member 1 43) := Context.conjunctionLeft hb2
  have he1 := Context.conjunctionRight (Context.conjunctionRight hb1)
  have he2 := Context.conjunctionRight (Context.conjunctionRight hb2)
  have hselected : Context Γ selectedGuard := Context.conjunctionIntro hs42
    (Context.conjunctionIntro hs43 (Context.conjunctionIntro hm02
      (Context.conjunctionIntro hm026 (Context.conjunctionIntro hm83
        (Context.conjunctionIntro hm827 (Context.conjunctionIntro (Context.conjunctionLeft he1)
          (Context.conjunctionIntro (Context.conjunctionLeft he2)
            (Context.conjunctionIntro (Context.conjunctionRight he1) (Context.conjunctionRight he2)))))))))
  exact .mp hselected (.mp hclean2 (.mp hsecond (.mp hclean1 (.mp hfirst
    (.closed selected_uniqueness_from_bijections)))))

private def guardFirstBody : Formula := namedBoth pathGuard firstBody
private def guardSecondExists : Formula := namedBoth pathGuard secondExists

private def eliminate_second : KDerivation (imp guardFirstBody.encode
    (imp secondExists.encode pointUniqueness)) := by
  have hp : KDerivation (imp guardFirstBody.encode (imp secondBody.encode pointUniqueness)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [secondBody.encode,guardFirstBody.encode]
    have hb : Context Γ secondBody.encode := .head _ _
    have hg : Context Γ guardFirstBody.encode := .hypothesis (by simp [Γ])
    exact .mp hb (.mp (Context.conjunctionRight hg) (.mp (Context.conjunctionLeft hg) (.closed selected)))
  have vg := free_vacuity 43 guardFirstBody (by decide)
  have vt : KDerivation (imp pointUniqueness (allCode 43 pointUniqueness)) := by
    simpa only [point_eq_code] using free_vacuity 43 pointEq (by decide)
  simpa only [secondExists,Formula.encode] using
    guarded_exists_left 43 guardFirstBody.encode secondBody.encode pointUniqueness vg vt hp

private def eliminate_first : KDerivation (imp guardSecondExists.encode
    (imp firstExists.encode pointUniqueness)) := by
  have hp : KDerivation (imp guardSecondExists.encode (imp firstBody.encode pointUniqueness)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [firstBody.encode,guardSecondExists.encode]
    have hb : Context Γ firstBody.encode := .head _ _
    have hg : Context Γ guardSecondExists.encode := .hypothesis (by simp [Γ])
    have hguard : Context Γ guardFirstBody.encode := Context.conjunctionIntro (Context.conjunctionLeft hg) hb
    exact .mp (Context.conjunctionRight hg) (.mp hguard (.closed eliminate_second))
  have vg := free_vacuity 42 guardSecondExists (by decide)
  have vt : KDerivation (imp pointUniqueness (allCode 42 pointUniqueness)) := by
    simpa only [point_eq_code] using free_vacuity 42 pointEq (by decide)
  simpa only [firstExists,Formula.encode] using
    guarded_exists_left 42 guardSecondExists.encode firstBody.encode pointUniqueness vg vt hp

private def from_paths : KDerivation (imp pathGuard.encode
    (imp spanPath.encode (imp movedPath.encode pointUniqueness))) := by
  have ha1 := (existentialAlpha 4 42 spanPathBody (by decide) (by decide) (by decide)).1
  have ha2 := (existentialAlpha 4 43 (replace 3 27 (replace 2 26 spanPathBody))
    (by decide) (by decide) (by decide)).1
  have h1 : KDerivation (imp spanPath.encode firstExists.encode) := by
    simpa only [spanPath,firstExists,firstBody,Formula.encode] using ha1
  have h2 : KDerivation (imp movedPath.encode secondExists.encode) := by
    simpa only [moved_path_shape,secondExists,secondBody,Formula.encode] using ha2
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [movedPath.encode,spanPath.encode,pathGuard.encode]
  have hp2 : Context Γ movedPath.encode := .head _ _
  have hp1 : Context Γ spanPath.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ pathGuard.encode := .hypothesis (by simp [Γ])
  have hex1 : Context Γ firstExists.encode := .mp hp1 (.closed h1)
  have hex2 : Context Γ secondExists.encode := .mp hp2 (.closed h2)
  have hguard : Context Γ guardSecondExists.encode := Context.conjunctionIntro hg hex2
  exact .mp hex1 (.mp hguard (.closed eliminate_first))

/-- Both path/path uniqueness directions follow under the displayed two
suffix bijections, clean graphs and actual whole endpoint memberships. -/
def path_uniqueness_from_bijections : KDerivation (imp pathGuard.encode
    (both pathSourceUnique pathTargetUnique)) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [pathGuard.encode]
  have hg : Context Γ pathGuard.encode := .head _ _
  have hs : Context Γ pathSourceUnique := by
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Δ := [equal 2 26,secondPath,firstPath,pathGuard.encode]
    have he : Context Δ (equal 2 26) := .head _ _
    have hp2 : Context Δ secondPath := .hypothesis (by simp [Δ])
    have hp1 : Context Δ firstPath := .hypothesis (by simp [Δ])
    have hg' : Context Δ pathGuard.encode := .hypothesis (by simp [Δ])
    have hpoint : Context Δ pointUniqueness := .mp hp2 (.mp hp1 (.mp hg' (.closed from_paths)))
    exact .mp he (Context.conjunctionLeft hpoint)
  have ht : Context Γ pathTargetUnique := by
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Δ := [equal 3 27,secondPath,firstPath,pathGuard.encode]
    have he : Context Δ (equal 3 27) := .head _ _
    have hp2 : Context Δ secondPath := .hypothesis (by simp [Δ])
    have hp1 : Context Δ firstPath := .hypothesis (by simp [Δ])
    have hg' : Context Δ pathGuard.encode := .hypothesis (by simp [Δ])
    have hpoint : Context Δ pointUniqueness := .mp hp2 (.mp hp1 (.mp hg' (.closed from_paths)))
    exact .mp he (Context.conjunctionRight hpoint)
  exact Context.conjunctionIntro hs ht

theorem path_uniqueness_from_bijections_certificate :
    theoremCode (certificate path_uniqueness_from_bijections) =
      imp pathGuard.encode (both pathSourceUnique pathTargetUnique) :=
  certificate_correct path_uniqueness_from_bijections

end PASoundness.PAtoCompactSeededSpanPathUniqueness

#print axioms PASoundness.PAtoCompactSeededSpanPathUniqueness.pathGuard
#print axioms PASoundness.PAtoCompactSeededSpanPathUniqueness.path_uniqueness_from_bijections
#print axioms PASoundness.PAtoCompactSeededSpanPathUniqueness.path_uniqueness_from_bijections_certificate
