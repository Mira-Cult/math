import PASoundness.SyntaxTransport
import PASoundness.Peano

/-! Capture-avoiding syntax identities for instantiating the PA induction step.
These are identities of PA syntax only; they do not establish a finite K proof
of the corresponding substitution compatibility or of PA induction. -/
namespace PASoundness.PAtoCompactInductionSubstitutionSyntax
open FirstOrder FirstOrder.Language
open PASoundness.SyntaxTransport

/-- A second substitution at the same variable composes with the first term.
The target term may contain the substituted variable, and the second variable
may coincide with it. The identity holds under arbitrary nested binders. -/
theorem substAt_same_comp (φ : Peano.Formula) (x : Nat) (t u : Peano.Term) :
    FOL.substAt (FOL.substAt φ x t) x u =
      FOL.substAt φ x (t.subst (fun z => if z = x then u else .var z)) := by
  unfold FOL.substAt
  rw [formula_subst_comp]
  congr 1
  funext z
  by_cases h : z = x <;> simp [h]

/-- Variable instantiation of the successor substitution in the PA induction
step yields the successor of that variable, including in the alias case x=y. -/
theorem subst_successor_then_variable (φ : Peano.Formula) (x y : Nat) :
    FOL.substAt (FOL.substAt φ x (Peano.succ (.var x))) x (.var y) =
      FOL.substAt φ x (Peano.succ (.var y)) := by
  rw [substAt_same_comp]
  congr 1
  simp only [Peano.succ, Term.subst]
  congr 1
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [Term.subst]

/-- Instantiating the PA induction step at a variable gives the expected
implication from the predicate at that variable to its successor instance. -/
theorem induction_step_subst_variable (φ : Peano.Formula) (x y : Nat) :
    FOL.substAt (φ.imp (FOL.substAt φ x (Peano.succ (.var x)))) x (.var y) =
      (FOL.substAt φ x (.var y)).imp (FOL.substAt φ x (Peano.succ (.var y))) := by
  change (FOL.substAt φ x (.var y)).imp
    (FOL.substAt (FOL.substAt φ x (Peano.succ (.var x))) x (.var y)) = _
  rw [subst_successor_then_variable]

end PASoundness.PAtoCompactInductionSubstitutionSyntax

#print axioms PASoundness.PAtoCompactInductionSubstitutionSyntax.substAt_same_comp
#print axioms PASoundness.PAtoCompactInductionSubstitutionSyntax.subst_successor_then_variable
#print axioms PASoundness.PAtoCompactInductionSubstitutionSyntax.induction_step_subst_variable
