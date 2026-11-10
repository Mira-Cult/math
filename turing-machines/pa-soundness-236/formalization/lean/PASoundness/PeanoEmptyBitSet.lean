import PASoundness.PeanoPowerGrowth

/-! The zero code is an empty bit set, proved inside the PA calculus. -/
namespace PASoundness.PeanoEmptyBitSet
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

private theorem less_var_zero_syntax : less (.var 0) zero =
    FOL.existsAt 5 ((add (.var 0) (succ (.var 5))).equal zero) := by
  simp [CompactArithmetic.less, CompactArithmetic.lessTemplate, CompactArithmetic.exAt,
    CompactArithmetic.v, FOL.existsAt, FOL.allAt, Peano.add, Peano.succ, Peano.zero,
    FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
    FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
    FirstOrder.Language.BoundedFormula.relabelAux]
  constructor
  · constructor
    · congr 1
      funext i
      fin_cases i
      · rfl
      · dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]
        congr 1
        funext j
        fin_cases j
        rfl
    · congr 1
      funext i
      exact Fin.elim0 i
  · rfl

private theorem no_less_zero_var : FormulaProves (less (.var 0) zero).not := by
  let row : Peano.Formula := (add (.var 0) (succ (.var 5))).equal zero
  have hrow : FormulaProves row.not := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    have he : FOL.Context Peano.Axiom [row]
        ((succ (add (.var 0) (.var 5))).equal zero) :=
      FOL.Context.eqTrans
        (.closed (FOL.Derivation.eqSymm (.axiom (.add_succ (.var 0) (.var 5)))))
        (FOL.Context.head [] row)
    exact .mp (.closed (.axiom (.succ_ne_zero (add (.var 0) (.var 5))))) he
  have hall : FormulaProves (FOL.allAt 5 row.not) := .generalize 5 hrow
  have hn : FormulaProves (FOL.allAt 5 row.not).not.not :=
    .mp (FOL.Derivation.doubleNegIntro _) hall
  rw [less_var_zero_syntax]
  exact hn

private theorem subst_not (φ : Peano.Formula) (σ : Nat → Peano.Term) :
    φ.not.subst σ = (φ.subst σ).not := by
  simp [FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.mapTermRel]
  rfl

/-- The exact compact strict order has no predecessor of zero, as a PA proof
for every arithmetic term. -/
theorem no_less_zero (t : Peano.Term) : FormulaProves (less t zero).not := by
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom)
      (.allElim (less (.var 0) zero).not 0 t)) (.generalize 0 no_less_zero_var)
  simpa [FOL.substAt, subst_not, less_subst, PeanoArithmetic.zero_subst,
    FirstOrder.Language.Term.subst] using h

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := by rfl

private theorem bit_position_zero (t : Peano.Term) :
    FormulaProves ((bitFormula zero t).imp (less t zero)) := by
  have hpower : FormulaProves (PeanoBitPositionReduction.power.imp
      (less PeanoBitPositionReduction.x PeanoBitPositionReduction.p)) :=
    PeanoPowerGrowth.power_growth (.var 1) (.var 2)
  have hbound := PeanoBitPositionReduction.witness_bound_of_components hpower
    PeanoAdditionAssociative.bit_shape_order
  have hpos := PeanoBitPositionReduction.bit_position_of_witness_bound hbound
  have hvars : FormulaProves ((bitFormula (.var 0) (.var 1)).imp (less (.var 1) (.var 0))) := hpos
  let φ : Peano.Formula := (bitFormula (.var 0) (.var 1)).imp (less (.var 1) (.var 0))
  have h₁ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim φ 0 zero)) (.generalize 0 hvars)
  have h₁' : FormulaProves ((bitFormula zero (.var 1)).imp (less (.var 1) zero)) := by
    simpa [FOL.substAt, φ, subst_imp, bitFormula_subst, less_subst,
      FirstOrder.Language.Term.subst] using h₁
  let ψ : Peano.Formula := (bitFormula zero (.var 1)).imp (less (.var 1) zero)
  have h₂ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim ψ 1 t)) (.generalize 1 h₁')
  simpa [FOL.substAt, ψ, subst_imp, bitFormula_subst, less_subst,
    PeanoArithmetic.zero_subst, FirstOrder.Language.Term.subst] using h₂

/-- The actual arithmetic bit predicate has no members at code zero. This is
a finite PA derivation for arbitrary terms, furnishing the empty-set base
needed by a bounded finite-code construction. -/
theorem zero_has_no_bit (t : Peano.Term) : FormulaProves (bitFormula zero t).not :=
  .mp (FOL.Derivation.contrapose (bit_position_zero t)) (no_less_zero t)

/-- The non-existential comprehension body after choosing the empty code.
The variable `x` is bound only in the universal conjunct; its occurrence in
the final conjunct is the original free value. -/
def emptyFilter (a : Peano.Term) (x : Nat) (ψ : Peano.Formula) : Peano.Formula :=
  (FOL.allAt x
    (((bitFormula a (.var x)).imp (ψ.imp (bitFormula zero (.var x)))) ⊓
      ((bitFormula zero (.var x)).imp ψ))) ⊓
    (ψ.imp (bitFormula zero (.var x)))

/-- PA derives the empty-code filtering body whenever the predicate is
universally false. This is a restricted object-level construction, not the
general parameterized comprehension scheme. -/
theorem empty_filter_of_everywhere_false (a : Peano.Term) (x : Nat) (ψ : Peano.Formula) :
    FormulaProves ((FOL.allAt x ψ.not).imp (emptyFilter a x ψ)) := by
  let H : Peano.Formula := FOL.allAt x ψ.not
  let bitA : Peano.Formula := bitFormula a (.var x)
  let bit0 : Peano.Formula := bitFormula zero (.var x)
  have htail : FOL.Context Peano.Axiom [H] (ψ.imp bit0) := by
    have hnot : FOL.Context Peano.Axiom [H] ψ.not := FOL.Context.allSelf (FOL.Context.head [] H)
    apply FOL.Context.deduction
    have hfalse : FOL.Context Peano.Axiom [ψ, H] (⊥ : Peano.Formula) :=
      .mp (FOL.Context.under hnot ψ) (FOL.Context.head [H] ψ)
    exact FOL.Context.explode bit0 hfalse
  have hsecond : FOL.Context Peano.Axiom [H] (bit0.imp ψ) := by
    apply FOL.Context.deduction
    have hfalse : FOL.Context Peano.Axiom [bit0, H] (⊥ : Peano.Formula) :=
      .mp (.closed (zero_has_no_bit (.var x))) (FOL.Context.head [H] bit0)
    exact FOL.Context.explode ψ hfalse
  have hall : FOL.Context Peano.Axiom [H]
      (FOL.allAt x ((bitA.imp (ψ.imp bit0)) ⊓ (bit0.imp ψ))) := by
    apply FOL.Context.generalize x
    · intro χ hχ
      have he : χ = H := by simpa only [List.mem_singleton] using hχ
      subst χ
      simp [H, SyntaxTransport.allAt_freeVars]
    · exact FOL.Context.conjunctionIntro (FOL.Context.lift htail bitA) hsecond
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  exact FOL.Context.conjunctionIntro hall htail

end PASoundness.PeanoEmptyBitSet
