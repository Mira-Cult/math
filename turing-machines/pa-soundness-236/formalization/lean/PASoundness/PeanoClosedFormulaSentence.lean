import PASoundness.Peano
import PASoundness.SyntaxTransport

/-! Convert a named PA formula with empty free-variable support to a genuine
PA sentence, without invoking PA soundness. -/
namespace PASoundness.PeanoClosedFormulaSentence
open FirstOrder FirstOrder.Language
open Peano

/-- The substitution merely changes the variable type: for a closed formula
the chosen closed zero term replaces no free occurrence. -/
def sentenceOf (φ : Peano.Formula) : Peano.Sentence :=
  φ.subst (fun _ => (.func Peano.FunctionSymbol.zero Fin.elim0 : Peano.language.Term Empty))

/-- The sentence's canonical open embedding is exactly the original closed
formula, as syntax. -/
theorem open_sentenceOf (φ : Peano.Formula) (hfree : φ.freeVarFinset = ∅) :
    FOL.openSentence (sentenceOf φ) = φ := by
  unfold FOL.openSentence sentenceOf
  rw [SyntaxTransport.formula_subst_relabel]
  calc
    _ = φ.subst Term.var := by
      apply SyntaxTransport.formula_subst_agree
      intro x hx
      simp [hfree] at hx
    _ = φ := SyntaxTransport.formula_subst_var φ

/-- Under the explicit closed-sentence soundness hypothesis, a PA derivation
of any closed named formula is true at every assignment. The hypothesis is
used on the concrete sentence produced by `sentenceOf`. -/
theorem realize_of_closed_soundness
    (hPA : ∀ s : Peano.Sentence, Peano.Proves s → Nat ⊨ s)
    (φ : Peano.Formula) (hfree : φ.freeVarFinset = ∅)
    (h : Peano.FormulaProves φ) (v : Nat → Nat) : φ.Realize v := by
  have hp : Peano.Proves (sentenceOf φ) := by
    change Peano.FormulaProves (FOL.openSentence (sentenceOf φ))
    rw [open_sentenceOf φ hfree]
    exact h
  have ht := hPA (sentenceOf φ) hp
  have hv := (FOL.realize_openSentence (sentenceOf φ) v).mpr ht
  rwa [open_sentenceOf φ hfree] at hv

end PASoundness.PeanoClosedFormulaSentence

#print axioms PASoundness.PeanoClosedFormulaSentence.realize_of_closed_soundness
