import PASoundness.PAtoCompactSeededSpanSeedOrder

/-! Pointwise order comparison for two explicit common-source witnesses. The
two source-to-image order clauses, endpoint memberships, and four original
graph edges are explicit. This is the selected-witness part of the remaining
path/path case; it does not yet eliminate the existential path witnesses. -/
namespace PASoundness.PAtoCompactSeededSpanSelectedPathOrder

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactOrderIsoInstance
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactSuccCongruenceOrderAlpha
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactSeededSpanOrderCases

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def frame : Formula := .imp oldOrderFresh orderMatrix
private def p1 : Formula := replace 2 42 frame
private def p2 : Formula := replace 4 43 p1
private def p3 : Formula := replace 3 2 p2
private def p4 : Formula := replace 5 26 p3
private def p5 : Formula := replace 0 25 p4
private def p6 : Formula := replace 1 0 p5
private def q1 : Formula := replace 2 42 frame
private def q2 : Formula := replace 4 43 q1
private def q3 : Formula := replace 5 27 q2
private def q4 : Formula := replace 0 25 q3
private def q5 : Formula := replace 1 8 q4
private def q6 : Formula := replace 25 1 q5

def firstOrder : Formula := replace 25 1 (replace 1 0 (replace 0 25 oldOrderFresh))
def secondOrder : Formula := replace 6 7 (replace 25 1 (replace 1 8 (replace 0 25 oldOrderFresh)))

def firstGuard : Formula := namedBoth (.member 1 42) (namedBoth (.member 1 43)
  (namedBoth (.member 0 2) (namedBoth (.member 0 26)
    (namedBoth (graphFormula 6 42 2) (graphFormula 6 43 26)))))
def secondGuard : Formula := namedBoth (.member 1 42) (namedBoth (.member 1 43)
  (namedBoth (.member 8 3) (namedBoth (.member 8 27)
    (namedBoth (graphFormula 7 42 3) (graphFormula 7 43 27)))))
private def firstCompare : Formula := namedBoth (.imp (.member 43 42) (.member 26 2))
  (.imp (.member 26 2) (.member 43 42))
private def secondCompare : Formula := namedBoth (.imp (.member 43 42) (.member 27 3))
  (.imp (.member 27 3) (.member 43 42))

private theorem first_alignment : replace 25 1 p6 = .imp firstOrder (.imp firstGuard firstCompare) := by decide
private theorem second_alignment : replace 6 7 q6 = .imp secondOrder (.imp secondGuard secondCompare) := by decide

private def original : KDerivation frame.encode := by
  simpa only [frame,Formula.encode] using compose order_unalpha order_instance

private def first_point : KDerivation (imp firstOrder.encode (imp firstGuard.encode firstCompare.encode)) := by
  have h1 := replace_derivation 2 42 frame (by decide) (by decide) original
  have h2 := replace_derivation 4 43 p1 (by decide) (by decide) (by simpa only [p1] using h1)
  have h3 := replace_derivation 3 2 p2 (by decide) (by decide) (by simpa only [p2] using h2)
  have h4 := replace_derivation 5 26 p3 (by decide) (by decide) (by simpa only [p3] using h3)
  have h5 := replace_derivation 0 25 p4 (by decide) (by decide) (by simpa only [p4] using h4)
  have h6 := replace_derivation 1 0 p5 (by decide) (by decide) (by simpa only [p5] using h5)
  have h7 := replace_derivation 25 1 p6 (by decide) (by decide) (by simpa only [p6] using h6)
  rw [first_alignment] at h7
  exact h7

private def second_point : KDerivation (imp secondOrder.encode (imp secondGuard.encode secondCompare.encode)) := by
  have h1 := replace_derivation 2 42 frame (by decide) (by decide) original
  have h2 := replace_derivation 4 43 q1 (by decide) (by decide) (by simpa only [q1] using h1)
  have h3 := replace_derivation 5 27 q2 (by decide) (by decide) (by simpa only [q2] using h2)
  have h4 := replace_derivation 0 25 q3 (by decide) (by decide) (by simpa only [q3] using h3)
  have h5 := replace_derivation 1 8 q4 (by decide) (by decide) (by simpa only [q4] using h4)
  have h6 := replace_derivation 25 1 q5 (by decide) (by decide) (by simpa only [q5] using h5)
  have h7 := replace_derivation 6 7 q6 (by decide) (by decide) (by simpa only [q6] using h6)
  rw [second_alignment] at h7
  exact h7

/-- Under the two actual guarded order instances, the selected witnesses
yield the desired comparison, in both directions. -/
def selected_path_order : KDerivation (imp firstOrder.encode (imp secondOrder.encode
    (imp firstGuard.encode (imp secondGuard.encode comparison)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [secondGuard.encode,firstGuard.encode,secondOrder.encode,firstOrder.encode]
  have hg2 : Context Γ secondGuard.encode := .head _ _
  have hg1 : Context Γ firstGuard.encode := .hypothesis (by simp [Γ])
  have ho2 : Context Γ secondOrder.encode := .hypothesis (by simp [Γ])
  have ho1 : Context Γ firstOrder.encode := .hypothesis (by simp [Γ])
  have hc1 : Context Γ firstCompare.encode := .mp hg1 (.mp ho1 (.closed first_point))
  have hc2 : Context Γ secondCompare.encode := .mp hg2 (.mp ho2 (.closed second_point))
  have hforward : Context Γ (imp (member 26 2) (member 27 3)) := by
    apply Context.deduction
    have ha : Context (member 26 2 :: Γ) (member 26 2) := .head _ _
    have hc1' : Context (member 26 2 :: Γ) firstCompare.encode := .under hc1 _
    have hc2' : Context (member 26 2 :: Γ) secondCompare.encode := .under hc2 _
    have hb : Context (member 26 2 :: Γ) (member 43 42) :=
      .mp ha (Context.conjunctionRight hc1')
    exact .mp hb (Context.conjunctionLeft hc2')
  have hreverse : Context Γ (imp (member 27 3) (member 26 2)) := by
    apply Context.deduction
    have ha : Context (member 27 3 :: Γ) (member 27 3) := .head _ _
    have hc1' : Context (member 27 3 :: Γ) firstCompare.encode := .under hc1 _
    have hc2' : Context (member 27 3 :: Γ) secondCompare.encode := .under hc2 _
    have hb : Context (member 27 3 :: Γ) (member 43 42) :=
      .mp ha (Context.conjunctionRight hc2')
    exact .mp hb (Context.conjunctionLeft hc1')
  exact Context.conjunctionIntro hforward hreverse

theorem selected_path_order_certificate : theoremCode (certificate selected_path_order) =
    imp firstOrder.encode (imp secondOrder.encode
      (imp firstGuard.encode (imp secondGuard.encode comparison))) := certificate_correct selected_path_order

end PASoundness.PAtoCompactSeededSpanSelectedPathOrder

#print axioms PASoundness.PAtoCompactSeededSpanSelectedPathOrder.firstOrder
#print axioms PASoundness.PAtoCompactSeededSpanSelectedPathOrder.secondOrder
#print axioms PASoundness.PAtoCompactSeededSpanSelectedPathOrder.firstGuard
#print axioms PASoundness.PAtoCompactSeededSpanSelectedPathOrder.secondGuard
#print axioms PASoundness.PAtoCompactSeededSpanSelectedPathOrder.selected_path_order
#print axioms PASoundness.PAtoCompactSeededSpanSelectedPathOrder.selected_path_order_certificate
