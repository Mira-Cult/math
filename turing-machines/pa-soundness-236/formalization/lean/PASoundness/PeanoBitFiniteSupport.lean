import PASoundness.PeanoPowerGrowth

/-! Object-level finite support of the exact arithmetic bit relation. -/
namespace PASoundness.PeanoBitFiniteSupport
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

private theorem bit_position_vars :
    FormulaProves ((bitFormula (.var 0) (.var 1)).imp (less (.var 1) (.var 0))) := by
  have hpower : FormulaProves (PeanoBitPositionReduction.power.imp
      (less PeanoBitPositionReduction.x PeanoBitPositionReduction.p)) :=
    PeanoPowerGrowth.power_growth (.var 1) (.var 2)
  have hbound := PeanoBitPositionReduction.witness_bound_of_components hpower
    PeanoAdditionAssociative.bit_shape_order
  exact PeanoBitPositionReduction.bit_position_of_witness_bound hbound

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := by rfl

/-- Any set bit has index strictly below its code. The proof constructs a PA
    derivation for arbitrary terms, including terms with shared variables. -/
theorem bit_position (a x : Peano.Term) :
    FormulaProves ((bitFormula a x).imp (less x a)) := by
  let k := a.varFinset.sup id + 2
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hfresh : k ∉ a.varFinset := by
    intro h
    have hle : k ≤ a.varFinset.sup id := Finset.le_sup (f := id) h
    dsimp [k] at hk hle
    omega
  let φ : Peano.Formula := (bitFormula (.var 0) (.var 1)).imp (less (.var 1) (.var 0))
  have h₁ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim φ 1 (.var k)))
    (.generalize 1 bit_position_vars)
  have h₁' : FormulaProves ((bitFormula (.var 0) (.var k)).imp (less (.var k) (.var 0))) := by
    simpa [FOL.substAt, φ, subst_imp, bitFormula_subst, less_subst,
      FirstOrder.Language.Term.subst] using h₁
  let ψ : Peano.Formula := (bitFormula (.var 0) (.var k)).imp (less (.var k) (.var 0))
  have h₂ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim ψ 0 a)) (.generalize 0 h₁')
  have h₂' : FormulaProves ((bitFormula a (.var k)).imp (less (.var k) a)) := by
    simpa [FOL.substAt, ψ, subst_imp, bitFormula_subst, less_subst,
      FirstOrder.Language.Term.subst, show k ≠ 0 by omega] using h₂
  let χ : Peano.Formula := (bitFormula a (.var k)).imp (less (.var k) a)
  have h₃ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim χ k x)) (.generalize k h₂')
  simpa [FOL.substAt, χ, subst_imp, bitFormula_subst, less_subst,
    FirstOrder.Language.Term.subst, FOL.term_subst_fresh a k x hfresh] using h₃

/-- A position not below the code cannot be a member. This gives the strict
    finite-support bound used by a bounded comprehension construction. -/
theorem no_bit_of_not_less (a x : Peano.Term) :
    FormulaProves ((less x a).not.imp (bitFormula a x).not) :=
  FOL.Derivation.contrapose (bit_position a x)

/-- Any strict upper bound on the code also bounds every set-bit position. -/
theorem bit_position_below_bound (a x bound : Peano.Term) :
    FormulaProves ((bitFormula a x).imp ((less a bound).imp (less x bound))) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hbit : FOL.Context Peano.Axiom [less a bound, bitFormula a x] (bitFormula a x) :=
    FOL.Context.under (FOL.Context.head [] _) _
  have hxa : FOL.Context Peano.Axiom [less a bound, bitFormula a x] (less x a) :=
    .mp (.closed (bit_position a x)) hbit
  exact .mp (.mp (.closed (PeanoOrderTransitive.less_transitive_all x a bound)) hxa)
    (FOL.Context.head _ _)

/-- When the code is strictly below a bound, positions outside that bound
    are not members of its bit set. -/
theorem no_bit_outside_bound (a x bound : Peano.Term) :
    FormulaProves ((less a bound).imp ((less x bound).not.imp (bitFormula a x).not)) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  let hbound : Peano.Formula := less a bound
  let hout : Peano.Formula := (less x bound).not
  let hbit : Peano.Formula := bitFormula a x
  have hp : FOL.Context Peano.Axiom [hbit, hout, hbound] hbit := FOL.Context.head _ _
  have hb : FOL.Context Peano.Axiom [hbit, hout, hbound] hbound :=
    FOL.Context.under (FOL.Context.under (FOL.Context.head [] hbound) hout) hbit
  have hl : FOL.Context Peano.Axiom [hbit, hout, hbound] (less x bound) :=
    .mp (.mp (.closed (bit_position_below_bound a x bound)) hp) hb
  have hn : FOL.Context Peano.Axiom [hbit, hout, hbound] hout :=
    FOL.Context.under (FOL.Context.head [hbound] hout) hbit
  exact .mp hn hl

end PASoundness.PeanoBitFiniteSupport
