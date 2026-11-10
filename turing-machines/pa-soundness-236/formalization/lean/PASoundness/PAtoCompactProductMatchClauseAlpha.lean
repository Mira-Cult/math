import PASoundness.PAtoCompactProductMatchExplicitIsomorphism
import PASoundness.PAtoCompactAlphaMapOne
import PASoundness.PAtoCompactOrderIsomorphism

/-! Rename private binders of the explicit product isomorphism clauses to
the literal canonical order-isomorphism syntax at safe endpoint names 40,42.
This is finite K alpha conversion; endpoint values may coincide. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchClauseAlpha

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactAlphaMapOne PASoundness.PAtoCompactProductMatchGraphOrder
open PASoundness.PAtoCompactProductMatchForwardBijectionClause PASoundness.PAtoCompactProductMatchReverseBijectionClause

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def highForward : Formula := replace 44 42 (replace 2 40 forwardClause)
def highReverse : Formula := replace 44 42 (replace 2 40 reverseClause)
def highOrder : Formula := replace 44 42 (replace 2 40 outputOrder)

def canonicalForward : Formula := .all 2 (.imp (.member 40 2) (.ex 3
  (namedBoth (.member 42 3) (namedBoth (graphFormula 58 2 3)
    (.all 4 (.imp (namedBoth (.member 42 4) (graphFormula 58 2 4)) (.equal 4 3)))))))
def canonicalReverse : Formula := .all 3 (.imp (.member 42 3) (.ex 2
  (namedBoth (.member 40 2) (namedBoth (graphFormula 58 2 3)
    (.all 4 (.imp (namedBoth (.member 40 4) (graphFormula 58 4 3)) (.equal 4 2)))))))
def canonicalOrder : Formula := replace 6 58 (replace 1 42 (replace 0 40 orderFormula))

def forwardAlpha : ProofEquiv highForward canonicalForward := by
  let A := highForward
  let B := mapNames (rename 32 2) A
  let C := mapNames (rename 35 3) B
  let D := mapNames (rename 55 4) C
  have h1 := alpha_map_one 32 2 A (by decide) (by decide) (by decide) (by decide)
  have h2 := alpha_map_one 35 3 B (by decide) (by decide) (by decide) (by decide)
  have h3 := alpha_map_one 55 4 C (by decide) (by decide) (by decide) (by decide)
  have hs : D = canonicalForward := by decide
  rw [← hs]
  exact h1.trans (h2.trans h3)

def reverseAlpha : ProofEquiv highReverse canonicalReverse := by
  let A := highReverse
  let B := mapNames (rename 55 3) A
  let C := mapNames (rename 32 2) B
  let D := mapNames (rename 52 4) C
  have h1 := alpha_map_one 55 3 A (by decide) (by decide) (by decide) (by decide)
  have h2 := alpha_map_one 32 2 B (by decide) (by decide) (by decide) (by decide)
  have h3 := alpha_map_one 52 4 C (by decide) (by decide) (by decide) (by decide)
  have hs : D = canonicalReverse := by decide
  rw [← hs]
  exact h1.trans (h2.trans h3)

def orderAlpha : ProofEquiv highOrder canonicalOrder := by
  let A := highOrder
  let B := mapNames (rename 32 2) A
  let C := mapNames (rename 52 4) B
  let D := mapNames (rename 35 3) C
  let E := mapNames (rename 55 5) D
  have h1 := alpha_map_one 32 2 A (by decide) (by decide) (by decide) (by decide)
  have h2 := alpha_map_one 52 4 B (by decide) (by decide) (by decide) (by decide)
  have h3 := alpha_map_one 35 3 C (by decide) (by decide) (by decide) (by decide)
  have h4 := alpha_map_one 55 5 D (by decide) (by decide) (by decide) (by decide)
  have hs : E = canonicalOrder := by decide
  rw [← hs]
  exact h1.trans (h2.trans (h3.trans h4))

theorem forward_alpha_certificate : theoremCode (certificate forwardAlpha.forward) =
    imp highForward.encode canonicalForward.encode := certificate_correct _
theorem reverse_alpha_certificate : theoremCode (certificate reverseAlpha.forward) =
    imp highReverse.encode canonicalReverse.encode := certificate_correct _
theorem order_alpha_certificate : theoremCode (certificate orderAlpha.forward) =
    imp highOrder.encode canonicalOrder.encode := certificate_correct _

end PASoundness.PAtoCompactProductMatchClauseAlpha

#print axioms PASoundness.PAtoCompactProductMatchClauseAlpha.forwardAlpha
#print axioms PASoundness.PAtoCompactProductMatchClauseAlpha.reverseAlpha
#print axioms PASoundness.PAtoCompactProductMatchClauseAlpha.orderAlpha
#print axioms PASoundness.PAtoCompactProductMatchClauseAlpha.forward_alpha_certificate
#print axioms PASoundness.PAtoCompactProductMatchClauseAlpha.reverse_alpha_certificate
#print axioms PASoundness.PAtoCompactProductMatchClauseAlpha.order_alpha_certificate
