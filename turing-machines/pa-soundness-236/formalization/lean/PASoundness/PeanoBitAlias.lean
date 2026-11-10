import PASoundness.PeanoBitFiniteSupport

/-! Literal AX8 alias case.  These lemmas rule out a code containing itself
inside PA and expose the quantified antecedent and the separate outer
occurrence in `comprehensionFormula b b c`.  They do not prove AX8. -/
namespace PASoundness.PeanoBitAlias
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

/-- A literal bit code cannot contain itself, for any PA term, including
terms with arbitrary free variables. -/
theorem bit_irreflexive (t : Peano.Term) : FormulaProves (bitFormula t t).not :=
  .mp (PeanoBitFiniteSupport.no_bit_of_not_less t t) (PeanoOrderIrreflexive.less_self t)

/-- Instantiating the aliased quantified antecedent substitutes the bound
name in *both* argument positions. -/
theorem alias_bit_subst (b : Nat) (t : Peano.Term) :
    FOL.substAt (bitFormula (.var b) (.var b)) b t = bitFormula t t := by
  simp [FOL.substAt, bitFormula_subst, FirstOrder.Language.Term.subst]

/-- The antecedent of the universally quantified AX8 forward implication
is vacuous in the alias case, uniformly for any consequent. -/
theorem alias_quantified_vacuity (b : Nat) (χ : Peano.Formula) :
    FormulaProves (FOL.allAt b ((bitFormula (.var b) (.var b)).imp χ)) := by
  apply FOL.Derivation.generalize
  exact FOL.Derivation.compose (bit_irreflexive (.var b)) (FOL.Derivation.explosion χ)

/-- In the literal alias case, the same name occurs twice *under* the
universal binder, while the final conjunct is outside that binder.  In
particular, this syntax equality does not freeze an input code under `∀ b`
or eliminate the separate occurrence of `b` outside `∀ b`.  The enclosing
existential may still bind that occurrence when `c = b`. -/
theorem comprehension_alias_syntax (b c : Nat) :
    CompactLogicalTransport.comprehensionFormula b b c =
      FOL.existsAt c
        ((FOL.allAt b
          (((bitFormula (.var b) (.var b)).imp
            ((CompactLogicalTransport.interpreted c).imp (bitFormula (.var c) (.var b)))) ⊓
           ((bitFormula (.var c) (.var b)).imp (CompactLogicalTransport.interpreted c)))) ⊓
         ((CompactLogicalTransport.interpreted c).imp (bitFormula (.var c) (.var b)))) := by
  rfl

/-- The separate bit formula outside `∀ b` really contains `b` free.
The exact enclosing binders are displayed by `comprehension_alias_syntax`. -/
theorem outer_bit_free (b c : Nat) :
    b ∈ (bitFormula (.var c) (.var b)).freeVarFinset := by
  simp [bitFormula_freeVars, FirstOrder.Language.Term.varFinset]

end PASoundness.PeanoBitAlias

#print axioms PASoundness.PeanoBitAlias.bit_irreflexive
#print axioms PASoundness.PeanoBitAlias.alias_bit_subst
#print axioms PASoundness.PeanoBitAlias.alias_quantified_vacuity
#print axioms PASoundness.PeanoBitAlias.comprehension_alias_syntax
#print axioms PASoundness.PeanoBitAlias.outer_bit_free
