import PASoundness.PeanoOrderIrreflexive
import PASoundness.PeanoBitPositionReduction
import Mathlib.Tactic.FinCases

/-! Object-level addition laws for the arithmetic bit-position proof. -/
namespace PASoundness.PeanoAdditionAssociative
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic

/-- Congruence of addition in its second argument, as a finite PA derivation. -/
theorem add_right_congr (t a b : Peano.Term) :
    FormulaProves ((a.equal b).imp ((add t a).equal (add t b))) := by
  obtain ⟨i, hi⟩ := FOL.fresh_for_term (add t a)
  have hi' : i ∉ t.varFinset ∧ i ∉ a.varFinset := by
    simpa [Peano.add, FirstOrder.Language.Term.varFinset] using hi
  let φ : Peano.Formula := (add t a).equal (add t (.var i))
  have h₀ : FOL.substAt φ i a = (add t a).equal (add t a) := by
    simp only [FOL.substAt, φ, FOL.equality_subst, add_subst,
      FirstOrder.Language.Term.subst, ↓reduceIte]
    rw [FOL.term_subst_fresh t i a hi'.1, FOL.term_subst_fresh a i a hi'.2]
  have h₁ : FOL.substAt φ i b = (add t a).equal (add t b) := by
    simp only [FOL.substAt, φ, FOL.equality_subst, add_subst,
      FirstOrder.Language.Term.subst, ↓reduceIte]
    rw [FOL.term_subst_fresh t i b hi'.1, FOL.term_subst_fresh a i b hi'.2]
  have h := FOL.Derivation.logical (Axiom := Peano.Axiom)
    (FOL.LogicalAxiom.eqSubst φ i a b)
  rw [h₀, h₁] at h
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  exact .mp (.mp (.closed h) (FOL.Context.head [] (a.equal b)))
    (.closed (.logical (.eqRefl _)))

/-- PA proves associativity for arbitrary arithmetic terms. The induction
variable is chosen fresh from both fixed terms, avoiding capture even when the
third term contains variables occurring in either fixed term. -/
theorem add_assoc (t u v : Peano.Term) :
    FormulaProves ((add (add t u) v).equal (add t (add u v))) := by
  obtain ⟨i, hi⟩ := FOL.fresh_for_term (add t u)
  have hi' : i ∉ t.varFinset ∧ i ∉ u.varFinset := by
    simpa [Peano.add, FirstOrder.Language.Term.varFinset] using hi
  let w : Peano.Term := .var i
  let φ : Peano.Formula := (add (add t u) w).equal (add t (add u w))
  have hbase : FormulaProves (FOL.substAt φ i zero) := by
    have h₁ := FOL.Derivation.axiom (Peano.Axiom.add_zero (add t u))
    have h₂ := FOL.Derivation.axiom (Peano.Axiom.add_zero u)
    have h₃ := FOL.Derivation.mp (add_right_congr t (add u zero) u) h₂
    have h := FOL.Derivation.eqTrans h₁ (FOL.Derivation.eqSymm h₃)
    simpa only [FOL.substAt, φ, w, FOL.equality_subst, add_subst, zero_subst,
      FirstOrder.Language.Term.subst, ↓reduceIte,
      FOL.term_subst_fresh t i zero hi'.1, FOL.term_subst_fresh u i zero hi'.2] using h
  have hstep : FormulaProves (φ.imp (FOL.substAt φ i (succ w))) := by
    have h₁ := FOL.Derivation.axiom (Peano.Axiom.add_succ (add t u) w)
    have h₂ := FOL.Derivation.axiom (Peano.Axiom.add_succ u w)
    have h₃ := FOL.Derivation.mp (add_right_congr t (add u (succ w)) (succ (add u w))) h₂
    have h₄ := FOL.Derivation.axiom (Peano.Axiom.add_succ t (add u w))
    have hright := FOL.Derivation.eqTrans h₃ h₄
    have hh : FormulaProves
        (φ.imp ((add (add t u) (succ w)).equal (add t (add u (succ w))))) := by
      apply FOL.Context.closeEmpty
      apply FOL.Context.deduction
      have hmid : FOL.Context Peano.Axiom [φ]
          ((succ (add (add t u) w)).equal (succ (add t (add u w)))) :=
        .mp (.closed (PeanoOrderIrreflexive.succ_congr _ _)) (FOL.Context.head [] φ)
      exact FOL.Context.eqTrans (FOL.Context.eqTrans (.closed h₁) hmid)
        (FOL.Context.eqSymm (.closed hright))
    simpa only [FOL.substAt, φ, w, FOL.equality_subst, add_subst, succ_subst,
      FirstOrder.Language.Term.subst, ↓reduceIte,
      FOL.term_subst_fresh t i (succ (.var i)) hi'.1,
      FOL.term_subst_fresh u i (succ (.var i)) hi'.2] using hh
  have hall : FormulaProves (FOL.allAt i φ) :=
    .mp (.mp (.axiom (.induction φ i)) hbase) (.generalize i hstep)
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim φ i v)) hall
  simpa only [FOL.substAt, φ, w, FOL.equality_subst, add_subst,
    FirstOrder.Language.Term.subst, ↓reduceIte,
    FOL.term_subst_fresh t i v hi'.1, FOL.term_subst_fresh u i v hi'.2] using h

/-- Successor commutes through the left side of addition, for arbitrary terms. -/
theorem add_succ_left (t u : Peano.Term) :
    FormulaProves ((add (succ t) u).equal (succ (add t u))) := by
  obtain ⟨i, hi⟩ := FOL.fresh_for_term t
  let w : Peano.Term := .var i
  let φ : Peano.Formula := (add (succ t) w).equal (succ (add t w))
  have hbase : FormulaProves (FOL.substAt φ i zero) := by
    have h₁ := FOL.Derivation.axiom (Peano.Axiom.add_zero (succ t))
    have h₂ := FOL.Derivation.axiom (Peano.Axiom.add_zero t)
    have h₃ := FOL.Derivation.mp (PeanoOrderIrreflexive.succ_congr (add t zero) t) h₂
    have h := FOL.Derivation.eqTrans h₁ (FOL.Derivation.eqSymm h₃)
    simpa only [FOL.substAt, φ, w, FOL.equality_subst, add_subst, succ_subst,
      zero_subst, FirstOrder.Language.Term.subst, ↓reduceIte,
      FOL.term_subst_fresh t i zero hi] using h
  have hstep : FormulaProves (φ.imp (FOL.substAt φ i (succ w))) := by
    have h₁ := FOL.Derivation.axiom (Peano.Axiom.add_succ (succ t) w)
    have h₂ := FOL.Derivation.axiom (Peano.Axiom.add_succ t w)
    have h₃ := FOL.Derivation.mp (PeanoOrderIrreflexive.succ_congr (add t (succ w))
      (succ (add t w))) h₂
    have hh : FormulaProves
        (φ.imp ((add (succ t) (succ w)).equal (succ (add t (succ w))))) := by
      apply FOL.Context.closeEmpty
      apply FOL.Context.deduction
      have hmid : FOL.Context Peano.Axiom [φ]
          ((succ (add (succ t) w)).equal (succ (succ (add t w)))) :=
        .mp (.closed (PeanoOrderIrreflexive.succ_congr _ _)) (FOL.Context.head [] φ)
      exact FOL.Context.eqTrans (FOL.Context.eqTrans (.closed h₁) hmid)
        (FOL.Context.eqSymm (.closed h₃))
    simpa only [FOL.substAt, φ, w, FOL.equality_subst, add_subst, succ_subst,
      FirstOrder.Language.Term.subst, ↓reduceIte,
      FOL.term_subst_fresh t i (succ (.var i)) hi] using hh
  have hall : FormulaProves (FOL.allAt i φ) :=
    .mp (.mp (.axiom (.induction φ i)) hbase) (.generalize i hstep)
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim φ i u)) hall
  simpa only [FOL.substAt, φ, w, FOL.equality_subst, add_subst, succ_subst,
    FirstOrder.Language.Term.subst, ↓reduceIte, FOL.term_subst_fresh t i u hi] using h

/-- PA proves commutativity of addition for arbitrary terms. -/
theorem add_comm (t u : Peano.Term) : FormulaProves ((add t u).equal (add u t)) := by
  obtain ⟨i, hi⟩ := FOL.fresh_for_term t
  let w : Peano.Term := .var i
  let φ : Peano.Formula := (add t w).equal (add w t)
  have hbase : FormulaProves (FOL.substAt φ i zero) := by
    have h₁ := FOL.Derivation.axiom (Peano.Axiom.add_zero t)
    have h₂ := PeanoArithmetic.zero_add t
    have h := FOL.Derivation.eqTrans h₁ (FOL.Derivation.eqSymm h₂)
    simpa only [FOL.substAt, φ, w, FOL.equality_subst, add_subst, zero_subst,
      FirstOrder.Language.Term.subst, ↓reduceIte,
      FOL.term_subst_fresh t i zero hi] using h
  have hstep : FormulaProves (φ.imp (FOL.substAt φ i (succ w))) := by
    have h₁ := FOL.Derivation.axiom (Peano.Axiom.add_succ t w)
    have h₂ := add_succ_left w t
    have hh : FormulaProves
        (φ.imp ((add t (succ w)).equal (add (succ w) t))) := by
      apply FOL.Context.closeEmpty
      apply FOL.Context.deduction
      have hmid : FOL.Context Peano.Axiom [φ]
          ((succ (add t w)).equal (succ (add w t))) :=
        .mp (.closed (PeanoOrderIrreflexive.succ_congr _ _)) (FOL.Context.head [] φ)
      exact FOL.Context.eqTrans (FOL.Context.eqTrans (.closed h₁) hmid)
        (FOL.Context.eqSymm (.closed h₂))
    simpa only [FOL.substAt, φ, w, FOL.equality_subst, add_subst, succ_subst,
      FirstOrder.Language.Term.subst, ↓reduceIte,
      FOL.term_subst_fresh t i (succ (.var i)) hi] using hh
  have hall : FormulaProves (FOL.allAt i φ) :=
    .mp (.mp (.axiom (.induction φ i)) hbase) (.generalize i hstep)
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim φ i u)) hall
  simpa only [FOL.substAt, φ, w, FOL.equality_subst, add_subst,
    FirstOrder.Language.Term.subst, ↓reduceIte, FOL.term_subst_fresh t i u hi] using h

/-- Congruence of addition in its first argument. -/
theorem add_left_congr (t a b : Peano.Term) :
    FormulaProves ((a.equal b).imp ((add a t).equal (add b t))) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have h : FOL.Context Peano.Axiom [a.equal b] ((add t a).equal (add t b)) :=
    .mp (.closed (add_right_congr t a b)) (FOL.Context.head [] (a.equal b))
  exact FOL.Context.eqTrans (FOL.Context.eqTrans (.closed (add_comm a t)) h)
    (.closed (add_comm t b))

/-- A witness rearrangement needed by the literal quotient/remainder row. -/
theorem arrange_witness (x Q d r : Peano.Term) :
    FormulaProves
      ((add (add Q (add x (succ d))) r).equal
        (add x (succ (add (add Q d) r)))) := by
  let X := add x (succ d)
  have e₁ := FOL.Derivation.eqSymm (add_assoc Q x (succ d))
  have e₂ := FOL.Derivation.mp (add_left_congr (succ d) (add Q x) (add x Q)) (add_comm Q x)
  have e₃ := add_assoc x Q (succ d)
  have e₄ := FOL.Derivation.mp (add_right_congr x (add Q (succ d)) (succ (add Q d)))
    (.axiom (.add_succ Q d))
  have e₅ : FormulaProves ((add Q X).equal (add x (succ (add Q d)))) :=
    FOL.Derivation.eqTrans (FOL.Derivation.eqTrans (FOL.Derivation.eqTrans e₁ e₂) e₃) e₄
  have e₆ := FOL.Derivation.mp (add_left_congr r (add Q X) (add x (succ (add Q d)))) e₅
  have e₇ := add_assoc x (succ (add Q d)) r
  have e₈ := FOL.Derivation.mp
    (add_right_congr x (add (succ (add Q d)) r) (succ (add (add Q d) r)))
    (add_succ_left (add Q d) r)
  exact FOL.Derivation.eqTrans (FOL.Derivation.eqTrans e₆ e₇) e₈

private theorem less_input_eq :
    CompactArithmetic.less (.var 1) (.var 2) =
      CompactArithmetic.exAt 5 ((add (.var 1) (succ (.var 5))).equal (.var 2)) := by
  simp [CompactArithmetic.less, CompactArithmetic.lessTemplate, CompactArithmetic.exAt,
    CompactArithmetic.v, FOL.allAt, Peano.add, Peano.succ,
    FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
    FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
    FirstOrder.Language.BoundedFormula.relabelAux]
  constructor
  · congr 1
    funext i
    fin_cases i
    · rfl
    · dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]
      congr 1
      funext j
      fin_cases j
      rfl
  · rfl

private theorem less_output_eq :
    CompactArithmetic.less (.var 1) (.var 0) =
      CompactArithmetic.exAt 5 ((add (.var 1) (succ (.var 5))).equal (.var 0)) := by
  simp [CompactArithmetic.less, CompactArithmetic.lessTemplate, CompactArithmetic.exAt,
    CompactArithmetic.v, FOL.allAt, Peano.add, Peano.succ,
    FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
    FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
    FirstOrder.Language.BoundedFormula.relabelAux]
  constructor
  · congr 1
    funext i
    fin_cases i
    · rfl
    · dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]
      congr 1
      funext j
      fin_cases j
      rfl
  · rfl

/-- PA derives the exact quotient/remainder order-propagation implication
required by `witness_bound_of_components`. The witness in the input `<`
relation is transformed into a witness for the output `<` relation using
only the displayed equation and PA addition laws. -/
theorem bit_shape_order :
    Peano.FormulaProves
      ((PeanoBitPositionReduction.a.equal
        (add (add (mul PeanoBitPositionReduction.q
          (add PeanoBitPositionReduction.p PeanoBitPositionReduction.p))
          PeanoBitPositionReduction.p) PeanoBitPositionReduction.r)).imp
        ((CompactArithmetic.less PeanoBitPositionReduction.x PeanoBitPositionReduction.p).imp
          PeanoBitPositionReduction.goal)) := by
  let A : Peano.Term := .var 0
  let X : Peano.Term := .var 1
  let P : Peano.Term := .var 2
  let Q : Peano.Term := mul (.var 3) (add P P)
  let R : Peano.Term := .var 4
  let D : Peano.Term := .var 5
  let shape : Peano.Formula := A.equal (add (add Q P) R)
  let input : Peano.Formula := (add X (succ D)).equal P
  let output : Peano.Formula := (add X (succ D)).equal A
  let witness : Peano.Term := add (add Q D) R
  have hw : Peano.FormulaProves (input.imp (shape.imp (CompactArithmetic.less X A))) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    have hinput : FOL.Context Peano.Axiom [shape, input] input :=
      FOL.Context.under (FOL.Context.head [] input) shape
    have hshape : FOL.Context Peano.Axiom [shape, input] shape :=
      FOL.Context.head [input] shape
    have he₁ : FOL.Context Peano.Axiom [shape, input]
        ((add Q P).equal (add Q (add X (succ D)))) :=
      .mp (.closed (add_right_congr Q P (add X (succ D)))) (FOL.Context.eqSymm hinput)
    have he₂ : FOL.Context Peano.Axiom [shape, input]
        ((add (add Q P) R).equal (add (add Q (add X (succ D))) R)) :=
      .mp (.closed (add_left_congr R _ _)) he₁
    have he₃ : FOL.Context Peano.Axiom [shape, input]
        ((add X (succ witness)).equal A) :=
      FOL.Context.eqSymm (FOL.Context.eqTrans (FOL.Context.eqTrans hshape he₂)
        (.closed (arrange_witness X Q D R)))
    have hsubst : FOL.substAt output 5 witness = (add X (succ witness)).equal A := by
      simp [FOL.substAt, output, X, A, D, FOL.equality_subst, add_subst, succ_subst,
        FirstOrder.Language.Term.subst]
    have hex : FOL.Context Peano.Axiom [shape, input] (FOL.existsAt 5 output) := by
      apply FOL.Context.mp (.closed (FOL.Derivation.existsIntro output 5 witness))
      rw [hsubst]
      exact he₃
    rw [less_output_eq]
    exact hex
  have hfresh : 5 ∉ (shape.imp (CompactArithmetic.less X A)).freeVarFinset := by decide
  have h := PeanoBitPositionReduction.exists_elim 5 hfresh hw
  have hout : Peano.FormulaProves
      (shape.imp ((FOL.existsAt 5 input).imp (CompactArithmetic.less X A))) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    exact .mp (.mp (.closed h) (FOL.Context.head [shape] (FOL.existsAt 5 input)))
      (FOL.Context.under (FOL.Context.head [] shape) _)
  simpa only [PeanoBitPositionReduction.a, PeanoBitPositionReduction.x,
    PeanoBitPositionReduction.p, PeanoBitPositionReduction.q, PeanoBitPositionReduction.r,
    PeanoBitPositionReduction.goal, A, X, P, Q, R, D, shape, input,
    less_input_eq, CompactArithmetic.exAt, FOL.existsAt] using hout

/-- Only the actual power-trace growth implication remains in this reduction
of the translated-bottom obligation. -/
theorem translated_bottom_of_power_growth
    (hpower : Peano.FormulaProves
      (PeanoBitPositionReduction.power.imp
        (CompactArithmetic.less PeanoBitPositionReduction.x PeanoBitPositionReduction.p))) :
    Peano.FormulaProves (CompactLogicalTransport.interpreted 1).not :=
  PeanoBitPositionReduction.translated_bottom_of_witness_bound
    (PeanoBitPositionReduction.witness_bound_of_components hpower bit_shape_order)

end PASoundness.PeanoAdditionAssociative
