import PASoundness.PAtoCompactSuccOrderOldOld
import PASoundness.CompactNamed

/-! The old/old point comparison for an unequal-top addition-successor graph
extension, with old source 31, old target 34, graph 6, and points 2–5. This
is a literal K derivation from the supplied old order and clean graph; it does
not construct a graph, prove the full extension, or establish PA arithmetic. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionSuccessorOldOld
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactGraphRestriction PASoundness.PAtoCompactSuccCongruenceData
open PASoundness.PAtoCompactSuccCongruenceOrderAlpha PASoundness.PAtoCompactSuccOrderOldOld
open PASoundness.PAtoCompactSuccOrderPointShape
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The original old order, with the two free endpoint inputs renamed. -/
def oldOrder : Formula := replace 1 34 (replace 0 31 orderFormula)
/-- Cleanliness for the same graph and the same old endpoints. -/
def oldClean : Formula := .all 19 (.imp (.member 6 19) (edgePredicate 19 31 34))
private def clean : Formula := .all 19 (.imp (.member 6 19) (edgePredicate 19 0 1))
private def cmp : Formula := namedBoth (.imp (.member 4 2) (.member 5 3))
  (.imp (.member 5 3) (.member 4 2))
private def body : Formula := .imp orderFormula (.imp clean (.imp (graphFormula 6 2 3)
  (.imp (graphFormula 6 4 5) cmp)))
private theorem clean_code : clean.encode = cleanGraph := by rfl
private theorem cmp_code : cmp.encode = comparison := by rfl

private def original : KDerivation body.encode := by
  change KDerivation (imp orderFormula.encode (imp cleanGraph
    (imp (graphFormula 6 2 3).encode (imp (graphFormula 6 4 5).encode comparison))))
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [orderFormula.encode]
  have ho : Context Γ orderFormula.encode := .head _ _
  have hf : Context Γ oldOrderFresh.encode := .mp ho (.closed order_alpha)
  exact .mp hf (.closed old_old)

private def moved : Formula := replace 0 31 body
private def original_at31 : KDerivation moved.encode := by
  have h := universalInstance 0 31 body (by decide) (by decide) (by decide)
  exact .mp (.generalize 0 original) h

/-- Two old graph edges obey the old order's comparison after capture-safe
specialization to source 31 and target 34. -/
def old_old_addition : KDerivation (imp oldOrder.encode (imp oldClean.encode
    (imp (graphFormula 6 2 3).encode (imp (graphFormula 6 4 5).encode comparison)))) := by
  have h := universalInstance 1 34 moved (by decide) (by decide) (by decide)
  have hc := KDerivation.mp (.generalize 1 original_at31) h
  have hs : replace 1 34 moved = .imp oldOrder (.imp oldClean (.imp (graphFormula 6 2 3)
    (.imp (graphFormula 6 4 5) cmp))) := by decide
  rw [hs] at hc
  simpa [Formula.encode,cmp_code] using hc

theorem old_old_addition_certificate : theoremCode (certificate old_old_addition) =
    imp oldOrder.encode (imp oldClean.encode
      (imp (graphFormula 6 2 3).encode (imp (graphFormula 6 4 5).encode comparison))) :=
  certificate_correct old_old_addition
end PASoundness.PAtoCompactAdditionSuccessorOldOld
#print axioms PASoundness.PAtoCompactAdditionSuccessorOldOld.old_old_addition
#print axioms PASoundness.PAtoCompactAdditionSuccessorOldOld.old_old_addition_certificate
