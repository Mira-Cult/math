import PASoundness.PAtoCompactSeededSpanBase
import PASoundness.PAtoCompactScopedActiveReplace

/-! Extract the two actual edge cases from a supplied seeded-span graph, for
two distinct syntactic point pairs. The second pair uses labels 26 and 27 so
that the common-path witness binder 4 is never captured. No order assertion,
graph existence, or candidate assumption is introduced. -/
namespace PASoundness.PAtoCompactSeededSpanOrderSplit

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactCommonSourceSpanBase PASoundness.PAtoCompactSeededSpanBase
open PASoundness.PAtoCompactScopedActiveReplace

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def orderPoint : Formula := .imp (namedBoth (.member 0 2) (.member 8 3))
  (namedBoth
    (.imp (graphFormula 9 2 3) (namedEither (graphFormula 14 2 3) spanPath))
    (.imp (namedEither (graphFormula 14 2 3) spanPath) (graphFormula 9 2 3)))

def movedPath : Formula := replace 3 27 (replace 2 26 spanPath)
def secondPoint : Formula := replace 3 27 (replace 2 26 orderPoint)

private theorem first_shape : seededSpan = .all 2 (.all 3 orderPoint) := by rfl
private theorem second_shape : secondPoint = .imp (namedBoth (.member 0 26) (.member 8 27))
  (namedBoth
    (.imp (graphFormula 9 26 27) (namedEither (graphFormula 14 26 27) movedPath))
    (.imp (namedEither (graphFormula 14 26 27) movedPath) (graphFormula 9 26 27))) := by decide

/-- The first output edge is either an actual seed edge or the retained
common-source path, under its two actual whole-membership guards. -/
def first_edge_split : KDerivation (imp seededSpan.encode
    (imp (both (member 0 2) (member 8 3))
      (imp (graphFormula 9 2 3).encode
        (either (graphFormula 14 2 3).encode spanPath.encode)))) := by
  have h2 := allSpecialize 2 (.all 3 orderPoint) (by decide)
  have h3 := allSpecialize 3 orderPoint (by decide)
  have hpoint : KDerivation (imp seededSpan.encode orderPoint.encode) := by
    simpa only [first_shape,Formula.encode] using compose h2 h3
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 9 2 3).encode,both (member 0 2) (member 8 3),seededSpan.encode]
  have he : Context Γ (graphFormula 9 2 3).encode := .head _ _
  have hm : Context Γ (both (member 0 2) (member 8 3)) := .hypothesis (by simp [Γ])
  have hs : Context Γ seededSpan.encode := .hypothesis (by simp [Γ])
  have hi := Context.conjunctionLeft (.mp hm (.mp hs (.closed hpoint)))
  exact .mp he hi

/-- The second edge is split using the same common-source path, with endpoints
26 and 27 and its witness binder kept distinct from both endpoints. -/
def second_edge_split : KDerivation (imp seededSpan.encode
    (imp (both (member 0 26) (member 8 27))
      (imp (graphFormula 9 26 27).encode
        (either (graphFormula 14 26 27).encode movedPath.encode)))) := by
  have h2 := universalInstance 2 26 (.all 3 orderPoint) (by decide) (by decide) (by decide)
  have hs2 : replace 2 26 (.all 3 orderPoint) = .all 3 (replace 2 26 orderPoint) := by decide
  rw [hs2] at h2
  have h3 := universalInstance 3 27 (replace 2 26 orderPoint) (by decide) (by decide) (by decide)
  have hp : KDerivation (imp seededSpan.encode secondPoint.encode) := by
    simpa only [first_shape,secondPoint,Formula.encode] using compose h2 h3
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 9 26 27).encode,both (member 0 26) (member 8 27),seededSpan.encode]
  have he : Context Γ (graphFormula 9 26 27).encode := .head _ _
  have hm : Context Γ (both (member 0 26) (member 8 27)) := .hypothesis (by simp [Γ])
  have hs : Context Γ seededSpan.encode := .hypothesis (by simp [Γ])
  have hpoint : Context Γ secondPoint.encode := .mp hs (.closed hp)
  rw [second_shape] at hpoint
  have hi := Context.conjunctionLeft (.mp hm hpoint)
  exact .mp he hi

theorem first_edge_split_certificate : theoremCode (certificate first_edge_split) =
    imp seededSpan.encode (imp (both (member 0 2) (member 8 3))
      (imp (graphFormula 9 2 3).encode
        (either (graphFormula 14 2 3).encode spanPath.encode))) := certificate_correct first_edge_split

theorem second_edge_split_certificate : theoremCode (certificate second_edge_split) =
    imp seededSpan.encode (imp (both (member 0 26) (member 8 27))
      (imp (graphFormula 9 26 27).encode
        (either (graphFormula 14 26 27).encode movedPath.encode))) := certificate_correct second_edge_split

end PASoundness.PAtoCompactSeededSpanOrderSplit

#print axioms PASoundness.PAtoCompactSeededSpanOrderSplit.orderPoint
#print axioms PASoundness.PAtoCompactSeededSpanOrderSplit.movedPath
#print axioms PASoundness.PAtoCompactSeededSpanOrderSplit.secondPoint
#print axioms PASoundness.PAtoCompactSeededSpanOrderSplit.first_edge_split
#print axioms PASoundness.PAtoCompactSeededSpanOrderSplit.second_edge_split
#print axioms PASoundness.PAtoCompactSeededSpanOrderSplit.first_edge_split_certificate
#print axioms PASoundness.PAtoCompactSeededSpanOrderSplit.second_edge_split_certificate
