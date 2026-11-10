import PASoundness.PeanoBetaUnique
import PASoundness.PeanoBetaCommonIncrement

/-! PA-syntactic transfer of a beta row through a common output witness. -/
namespace PASoundness.PeanoBetaRowTransfer
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic

/-- Equality of output terms transports the literal beta formula inside PA. -/
theorem beta_output_congr (b c i r s : Peano.Term) :
    FormulaProves ((r.equal s).imp ((beta b c i r).imp (beta b c i s))) := by
  obtain ⟨j, hj⟩ := FOL.fresh_for_term (add b (add c i))
  have hj' : j ∉ b.varFinset ∧ j ∉ c.varFinset ∧ j ∉ i.varFinset := by
    simpa [Peano.add, FirstOrder.Language.Term.varFinset] using hj
  let φ : Peano.Formula := beta b c i (.var j)
  have h₀ : FOL.substAt φ j r = beta b c i r := by
    simp only [FOL.substAt, φ, beta_subst, FirstOrder.Language.Term.subst, ↓reduceIte,
      FOL.term_subst_fresh b j r hj'.1, FOL.term_subst_fresh c j r hj'.2.1,
      FOL.term_subst_fresh i j r hj'.2.2]
  have h₁ : FOL.substAt φ j s = beta b c i s := by
    simp only [FOL.substAt, φ, beta_subst, FirstOrder.Language.Term.subst, ↓reduceIte,
      FOL.term_subst_fresh b j s hj'.1, FOL.term_subst_fresh c j s hj'.2.1,
      FOL.term_subst_fresh i j s hj'.2.2]
  have h := FOL.Derivation.logical (Axiom := Peano.Axiom)
    (FOL.LogicalAxiom.eqSubst φ j r s)
  rw [h₀, h₁] at h
  exact h

/-- A common literal beta output transfers the previously known row. The
witness name must be absent from the old and new rows in the conclusion;
this is the eigenvariable condition needed for existential elimination. -/
theorem common_output_transfer (b c b' c' i r : Peano.Term) (w : Nat)
    (fresh : w ∉ ((beta b c i r).imp (beta b' c' i r)).freeVarFinset) :
    FormulaProves ((FOL.existsAt w
      ((beta b c i (.var w)) ⊓ (beta b' c' i (.var w)))).imp
      ((beta b c i r).imp (beta b' c' i r))) := by
  let A := beta b c i (.var w)
  let B := beta b' c' i (.var w)
  let O := beta b c i r
  let T := beta b' c' i r
  have hbody : FormulaProves ((A ⊓ B).imp (O.imp T)) := by
    let Γ := [O, A ⊓ B]
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    have hp : FOL.Context Peano.Axiom Γ (A ⊓ B) := .hypothesis (by simp [Γ])
    have ho : FOL.Context Peano.Axiom Γ O := FOL.Context.head _ _
    have hA : FOL.Context Peano.Axiom Γ A := FOL.Context.conjunctionLeft hp
    have hB : FOL.Context Peano.Axiom Γ B := FOL.Context.conjunctionRight hp
    have heq : FOL.Context Peano.Axiom Γ ((.var w : Peano.Term).equal r) :=
      .mp (.mp (.closed (PeanoBetaUnique.beta_unique b c i (.var w) r)) hA) ho
    exact .mp (.mp (.closed (beta_output_congr b' c' i (.var w) r)) heq) hB
  exact PeanoBitPositionReduction.exists_elim w fresh hbody

end PASoundness.PeanoBetaRowTransfer

#print axioms PASoundness.PeanoBetaRowTransfer.beta_output_congr
#print axioms PASoundness.PeanoBetaRowTransfer.common_output_transfer
