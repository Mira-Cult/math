import PASoundness.PAtoCompactSeededSpanSelectedPathOrder
import PASoundness.PAtoCompactSuccGraphOutputLift
import PASoundness.PAtoCompactFreeVacuity

/-! The path/path order case, from two supplied common-source-to-image order
clauses and the four actual endpoint memberships. Both common-source path
witnesses are alpha-renamed and eliminated inside K. -/
namespace PASoundness.PAtoCompactSeededSpanPathOrder

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactCommonSourceSpanBase PASoundness.PAtoCompactSeededSpanOrderSplit
open PASoundness.PAtoCompactSeededSpanOrderCases PASoundness.PAtoCompactSeededSpanOrderMixedAssembly
open PASoundness.PAtoCompactSeededSpanSelectedPathOrder PASoundness.PAtoCompactSuccGraphOutputLift
open PASoundness.PAtoCompactFreeVacuity

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def orderGuard : Formula := namedBoth firstOrder (namedBoth secondOrder
  (namedBoth (.member 0 2) (namedBoth (.member 0 26)
    (namedBoth (.member 8 3) (.member 8 27)))))
private def firstBody : Formula := replace 4 42 spanPathBody
private def secondBody : Formula := replace 4 43 (replace 3 27 (replace 2 26 spanPathBody))
private def firstExists : Formula := .ex 42 firstBody
private def secondExists : Formula := .ex 43 secondBody
private def compareFormula : Formula := namedBoth (.imp (.member 26 2) (.member 27 3))
  (.imp (.member 27 3) (.member 26 2))
private theorem compare_code : compareFormula.encode = comparison := by rfl
private theorem moved_path_shape : movedPath =
    .ex 4 (replace 3 27 (replace 2 26 spanPathBody)) := by decide

private def selected : KDerivation (imp orderGuard.encode
    (imp firstBody.encode (imp secondBody.encode comparison))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [secondBody.encode,firstBody.encode,orderGuard.encode]
  have hb2 : Context Γ secondBody.encode := .head _ _
  have hb1 : Context Γ firstBody.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ orderGuard.encode := .hypothesis (by simp [Γ])
  have ho1 : Context Γ firstOrder.encode := Context.conjunctionLeft hg
  have hr := Context.conjunctionRight hg
  have ho2 : Context Γ secondOrder.encode := Context.conjunctionLeft hr
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
  have hfirst : Context Γ firstGuard.encode := Context.conjunctionIntro hs42
    (Context.conjunctionIntro hs43 (Context.conjunctionIntro hm02
      (Context.conjunctionIntro hm026 (Context.conjunctionIntro
        (Context.conjunctionLeft he1) (Context.conjunctionLeft he2)))))
  have hsecond : Context Γ secondGuard.encode := Context.conjunctionIntro hs42
    (Context.conjunctionIntro hs43 (Context.conjunctionIntro hm83
      (Context.conjunctionIntro hm827 (Context.conjunctionIntro
        (Context.conjunctionRight he1) (Context.conjunctionRight he2)))))
  exact .mp hsecond (.mp hfirst (.mp ho2 (.mp ho1 (.closed selected_path_order))))

private def guardFirstBody : Formula := namedBoth orderGuard firstBody
private def guardSecondExists : Formula := namedBoth orderGuard secondExists

private def eliminate_second : KDerivation (imp guardFirstBody.encode
    (imp secondExists.encode comparison)) := by
  have hp : KDerivation (imp guardFirstBody.encode (imp secondBody.encode comparison)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [secondBody.encode,guardFirstBody.encode]
    have hb : Context Γ secondBody.encode := .head _ _
    have hg : Context Γ guardFirstBody.encode := .hypothesis (by simp [Γ])
    exact .mp hb (.mp (Context.conjunctionRight hg)
      (.mp (Context.conjunctionLeft hg) (.closed selected)))
  have vg := free_vacuity 43 guardFirstBody (by decide)
  have vt : KDerivation (imp comparison (allCode 43 comparison)) := by
    simpa only [compare_code] using free_vacuity 43 compareFormula (by decide)
  simpa only [secondExists,Formula.encode] using
    guarded_exists_left 43 guardFirstBody.encode secondBody.encode comparison vg vt hp

private def eliminate_first : KDerivation (imp guardSecondExists.encode
    (imp firstExists.encode comparison)) := by
  have hp : KDerivation (imp guardSecondExists.encode (imp firstBody.encode comparison)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [firstBody.encode,guardSecondExists.encode]
    have hb : Context Γ firstBody.encode := .head _ _
    have hg : Context Γ guardSecondExists.encode := .hypothesis (by simp [Γ])
    have hguard : Context Γ guardFirstBody.encode :=
      Context.conjunctionIntro (Context.conjunctionLeft hg) hb
    exact .mp (Context.conjunctionRight hg) (.mp hguard (.closed eliminate_second))
  have vg := free_vacuity 42 guardSecondExists (by decide)
  have vt : KDerivation (imp comparison (allCode 42 comparison)) := by
    simpa only [compare_code] using free_vacuity 42 compareFormula (by decide)
  simpa only [firstExists,Formula.encode] using
    guarded_exists_left 42 guardSecondExists.encode firstBody.encode comparison vg vt hp

/-- The two actual common-source paths yield order agreement. The source
orders and all four endpoint memberships remain in `orderGuard`. -/
def path_path_from_orders : KDerivation (imp orderGuard.encode pathPath) := by
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
  let Γ := [movedPath.encode,spanPath.encode,orderGuard.encode]
  have hp2 : Context Γ movedPath.encode := .head _ _
  have hp1 : Context Γ spanPath.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ orderGuard.encode := .hypothesis (by simp [Γ])
  have hex1 : Context Γ firstExists.encode := .mp hp1 (.closed h1)
  have hex2 : Context Γ secondExists.encode := .mp hp2 (.closed h2)
  have hguard : Context Γ guardSecondExists.encode := Context.conjunctionIntro hg hex2
  exact .mp hex1 (.mp hguard (.closed eliminate_first))

theorem path_path_from_orders_certificate : theoremCode (certificate path_path_from_orders) =
    imp orderGuard.encode pathPath := certificate_correct path_path_from_orders

end PASoundness.PAtoCompactSeededSpanPathOrder

#print axioms PASoundness.PAtoCompactSeededSpanPathOrder.orderGuard
#print axioms PASoundness.PAtoCompactSeededSpanPathOrder.path_path_from_orders
#print axioms PASoundness.PAtoCompactSeededSpanPathOrder.path_path_from_orders_certificate
