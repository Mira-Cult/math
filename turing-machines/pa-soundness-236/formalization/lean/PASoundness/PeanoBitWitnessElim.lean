import PASoundness.PeanoBitPositionReduction

/-! Capture-safe elimination of literal bit witnesses toward an arbitrary goal. -/
namespace PASoundness.PeanoBitWitnessElim
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic PeanoBitPositionReduction

private theorem template_as_bit : bitFormula a x = bitTemplate := by
  unfold bitFormula
  calc
    bitTemplate.subst (fun y => if y = 0 then a else if y = 1 then x else zero) =
        bitTemplate.subst Term.var := by
      apply SyntaxTransport.formula_subst_agree
      intro y hy
      simp only [bitTemplate_freeVars, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl <;> rfl
    _ = bitTemplate := SyntaxTransport.formula_subst_var _

/-- Given an explicit PA derivation from a literal bit row and power witness,
eliminate all three existential witnesses to reach any conclusion that has none
of their names free. This proves only a derivation transformation; it does not
supply the derivation premise. -/
theorem bit_elim (φ : Peano.Formula)
    (hf2 : 2 ∉ φ.freeVarFinset) (hf3 : 3 ∉ φ.freeVarFinset)
    (hf4 : 4 ∉ φ.freeVarFinset)
    (hrow : FormulaProves (row.imp (power.imp φ))) :
    FormulaProves ((bitFormula a x).imp φ) := by
  have hp4 : 4 ∉ power.freeVarFinset := by decide
  have hp3 : 3 ∉ power.freeVarFinset := by decide
  have h4 : 4 ∉ (power.imp φ).freeVarFinset := by
    simpa only [BoundedFormula.freeVarFinset, Finset.mem_union, not_or] using ⟨hp4, hf4⟩
  have h3 : 3 ∉ (power.imp φ).freeVarFinset := by
    simpa only [BoundedFormula.freeVarFinset, Finset.mem_union, not_or] using ⟨hp3, hf3⟩
  have e4 := exists_elim 4 h4 hrow
  have e3 := exists_elim 3 h3 e4
  have hbody : FormulaProves
      ((power ⊓ FOL.existsAt 3 (FOL.existsAt 4 row)).imp φ) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    have hconj : FOL.Context Peano.Axiom
        [power ⊓ FOL.existsAt 3 (FOL.existsAt 4 row)]
        (power ⊓ FOL.existsAt 3 (FOL.existsAt 4 row)) := FOL.Context.head [] _
    exact .mp (.mp (.closed e3) (FOL.Context.conjunctionRight hconj))
      (FOL.Context.conjunctionLeft hconj)
  have h := exists_elim 2 hf2 hbody
  rw [template_as_bit]
  simpa only [bitTemplate, CompactArithmetic.exAt, a, x, p, q, r, row, power,
    CompactArithmetic.v, FOL.existsAt] using h

end PASoundness.PeanoBitWitnessElim

#print axioms PASoundness.PeanoBitWitnessElim.bit_elim
