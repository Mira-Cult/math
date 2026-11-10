import PASoundness.PAtoCompactMulReversalFormulaNaturality

/-! Multiplication reversal preserves the exact full PA induction schema.
This is an equality of finite formulas. It does not by itself construct a
compact proof or establish soundness. -/

namespace PASoundness.PAtoCompactMulReversalInduction

open FirstOrder FirstOrder.Language
open PASoundness.PAtoCompactMulReversalSyntax
open PASoundness.PAtoCompactMulReversalFormulaNaturality

/-- Capture-avoiding substitutions at zero and the successor of the induction
variable, both named quantifiers, and all implication nodes are preserved.
All other free variables of the formula remain parameters. -/
theorem reverse_inductionAxiom (φ : Peano.Formula) (x : Nat) :
    reverseBounded 0 (Peano.inductionAxiom φ x) =
      Peano.inductionAxiom (reverseBounded 0 φ) x := by
  simp only [Peano.inductionAxiom, reverseBounded_imp, reverse_allAt,
    reverse_substAt, reverseTerm_zero, reverseTerm_succ, reverseTerm_var]

end PASoundness.PAtoCompactMulReversalInduction

#print axioms PASoundness.PAtoCompactMulReversalInduction.reverse_inductionAxiom
