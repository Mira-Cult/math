import PASoundness.PAtoCompactPartialCompositionBackwardLift
import PASoundness.PAtoCompactPartialCompositionBackwardPoint
import PASoundness.PAtoCompactCompositionSuppliedVacuity
import PASoundness.PAtoCompactPartialCompositionInstantiate

/-! Quantified backward coverage under the supplied named successor context.
The old invariant, selected path, pair and adjunction remain explicit; this
constructs neither the extended graph nor a global induction. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialCompositionBackwardAll
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactCompositionNoSpurious
open PASoundness.PAtoCompactCompositionSelectedImages PASoundness.PAtoCompactCompositionSuppliedVacuity
open PASoundness.PAtoCompactPartialCompositionBase PASoundness.PAtoCompactPartialCompositionInstantiate
open PASoundness.PAtoCompactPartialCompositionBackwardNew PASoundness.PAtoCompactPartialCompositionBackwardPoint
open PASoundness.PAtoCompactPartialCompositionBackwardLift
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The supplied context and old invariant establish one guarded query. -/
def pointwise : KDerivation (imp suppliedPremises.encode (imp partialComposition.encode
    (imp (both (member 0 2) (member 8 3))
      (imp (graphFormula 17 2 3).encode (both (member 13 2) path.encode))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 17 2 3).encode,both (member 0 2) (member 8 3),
    partialComposition.encode,suppliedPremises.encode]
  have hn : Context Γ (graphFormula 17 2 3).encode := Context.head _ _
  have hy : Context Γ (both (member 0 2) (member 8 3)) := .hypothesis (by simp [Γ])
  have ho : Context Γ partialComposition.encode := .hypothesis (by simp [Γ])
  have hp : Context Γ suppliedPremises.encode := .hypothesis (by simp [Γ])
  have hfirst : Context Γ firstImageBody.encode := Context.conjunctionLeft hp
  have ht₁ := Context.conjunctionRight hp
  have hsecond : Context Γ secondImageBody.encode := Context.conjunctionLeft ht₁
  have ht₂ := Context.conjunctionRight ht₁
  have hs : Context Γ (successorCode 10 13 15) := Context.conjunctionLeft ht₂
  have ht₃ := Context.conjunctionRight ht₂
  have hpair : Context Γ selected := Context.conjunctionLeft ht₃
  have ht₄ := Context.conjunctionRight ht₃
  have hadj : Context Γ adjacent := Context.conjunctionLeft ht₄
  have hm : Context Γ (member 1 11) := Context.conjunctionLeft hfirst
  have hf : Context Γ (graphFormula 6 10 11).encode :=
    Context.conjunctionLeft (Context.conjunctionRight hfirst)
  have hg : Context Γ (graphFormula 7 11 12).encode :=
    Context.conjunctionLeft (Context.conjunctionRight hsecond)
  have hx : Context Γ pointFormula.encode := .mp ho (.closed partial_composition_instance)
  rw [point_formula_code] at hx
  have hback : Context Γ (imp (graphFormula 9 2 3).encode
      (both (member 10 2) path.encode)) := Context.conjunctionLeft (.mp hy hx)
  exact .mp hn (.mp hg (.mp hf (.mp hm (.mp hpair (.mp hadj
    (.mp hback (.mp hs (.closed backward_point))))))))

/-- Quantify both queried coordinates with supplied-context and invariant
vacuity proven by capture-safe freshening. -/
def backward_all : KDerivation
    (imp suppliedPremises.encode (imp partialComposition.encode backwardFormula.encode)) :=
  backward_lift suppliedPremises vacuity_2 vacuity_3
    partial_composition_vacuity_2 partial_composition_vacuity_3 pointwise

theorem backward_all_certificate : theoremCode (certificate backward_all) =
    imp suppliedPremises.encode (imp partialComposition.encode backwardFormula.encode) :=
  certificate_correct backward_all

/-- The old invariant is already the last conjunct of suppliedPremises. -/
def backward_all_from_premises : KDerivation
    (imp suppliedPremises.encode backwardFormula.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  have hp : Context [suppliedPremises.encode] suppliedPremises.encode := Context.head [] _
  have hold : Context [suppliedPremises.encode] partialComposition.encode :=
    Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight
      (Context.conjunctionRight (Context.conjunctionRight hp))))
  exact .mp hold (.mp hp (.closed backward_all))

theorem backward_all_from_premises_certificate :
    theoremCode (certificate backward_all_from_premises) =
      imp suppliedPremises.encode backwardFormula.encode :=
  certificate_correct backward_all_from_premises

end PASoundness.PAtoCompactPartialCompositionBackwardAll

#print axioms PASoundness.PAtoCompactPartialCompositionBackwardAll.backward_all
#print axioms PASoundness.PAtoCompactPartialCompositionBackwardAll.backward_all_certificate
#print axioms PASoundness.PAtoCompactPartialCompositionBackwardAll.backward_all_from_premises
#print axioms PASoundness.PAtoCompactPartialCompositionBackwardAll.backward_all_from_premises_certificate
