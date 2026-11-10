import PASoundness.PeanoBetaRowTransfer

/-! PA equality substitution for the arithmetic bit code. -/
namespace PASoundness.PeanoBitCodeCongruence
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

/-- PA transports a literal bit formula along equality of its code terms.
The index and code terms may share free variables; the substitution name is
chosen fresh for the index. -/
theorem bit_code_congr (a b i : Peano.Term) :
    FormulaProves ((a.equal b).imp ((bitFormula a i).imp (bitFormula b i))) := by
  obtain ⟨j, hj⟩ := FOL.fresh_for_term i
  let φ : Peano.Formula := bitFormula (.var j) i
  have ha : FOL.substAt φ j a = bitFormula a i := by
    simp only [FOL.substAt, φ, bitFormula_subst, FirstOrder.Language.Term.subst,
      ↓reduceIte, FOL.term_subst_fresh i j a hj]
  have hb : FOL.substAt φ j b = bitFormula b i := by
    simp only [FOL.substAt, φ, bitFormula_subst, FirstOrder.Language.Term.subst,
      ↓reduceIte, FOL.term_subst_fresh i j b hj]
  have h := FOL.Derivation.logical (Axiom := Peano.Axiom)
    (FOL.LogicalAxiom.eqSubst φ j a b)
  rw [ha, hb] at h
  exact h

/-- PA derives both directions for commuting the two summands of a code. -/
theorem bit_add_comm (a p i : Peano.Term) : FormulaProves
    (((bitFormula (add a p) i).imp (bitFormula (add p a) i)) ⊓
      ((bitFormula (add p a) i).imp (bitFormula (add a p) i))) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.conjunctionIntro
  · exact .mp (.closed (bit_code_congr (add a p) (add p a) i))
      (.closed (PeanoAdditionAssociative.add_comm a p))
  · exact .mp (.closed (bit_code_congr (add p a) (add a p) i))
      (.closed (PeanoAdditionAssociative.add_comm p a))

end PASoundness.PeanoBitCodeCongruence

#print axioms PASoundness.PeanoBitCodeCongruence.bit_code_congr
#print axioms PASoundness.PeanoBitCodeCongruence.bit_add_comm
