import PASoundness.PeanoAdditionAssociative
import PASoundness.PeanoMultiplication

/-! A genuine PA product step for adjacent quotient comparisons. -/
namespace PASoundness.PeanoMultiplyQuotientStep
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoAdditionAssociative PeanoMultiplication

/-- Swap the two trailing summands in the actual arithmetic calculus. -/
theorem swap_add_tail (a b c : Peano.Term) :
    FormulaProves ((add (add a b) c).equal (add (add a c) b)) := by
  have h := FOL.Derivation.mp (add_right_congr a (add b c) (add c b)) (add_comm b c)
  exact FOL.Derivation.eqTrans (FOL.Derivation.eqTrans (add_assoc a b c) h)
    (FOL.Derivation.eqSymm (add_assoc a c b))

private theorem swap_successor_tail (a b c : Peano.Term) :
    FormulaProves ((add (add a b) (succ c)).equal (add (add a c) (succ b))) := by
  have h := FOL.Derivation.mp (PeanoOrderIrreflexive.succ_congr _ _) (swap_add_tail a b c)
  exact FOL.Derivation.eqTrans
    (FOL.Derivation.eqTrans (.axiom (.add_succ (add a b) c)) h)
    (FOL.Derivation.eqSymm (.axiom (.add_succ (add a c) b)))

/-- The gap between consecutive quotient products is precisely the modulus:
PA derives `(S q)*m = q*m + m` for arbitrary arithmetic terms. -/
theorem mul_succ_left (q m : Peano.Term) :
    FormulaProves ((mul (succ q) m).equal (add (mul q m) m)) := by
  obtain ⟨i, hi⟩ := FOL.fresh_for_term q
  let w : Peano.Term := .var i
  let φ : Peano.Formula := (mul (succ q) w).equal (add (mul q w) w)
  have hbase : FormulaProves (FOL.substAt φ i zero) := by
    have h₁ := FOL.Derivation.axiom (Peano.Axiom.mul_zero (succ q))
    have h₂ : FormulaProves ((add (mul q zero) zero).equal zero) :=
      FOL.Derivation.eqTrans (.axiom (.add_zero (mul q zero)))
      (.axiom (.mul_zero q))
    have h := FOL.Derivation.eqTrans h₁ (FOL.Derivation.eqSymm h₂)
    simpa only [FOL.substAt, φ, w, FOL.equality_subst, add_subst, succ_subst,
      mul_subst, PeanoArithmetic.zero_subst, FirstOrder.Language.Term.subst, ↓reduceIte,
      FOL.term_subst_fresh q i zero hi] using h
  have hstep : FormulaProves (φ.imp (FOL.substAt φ i (succ w))) := by
    have h₁ := FOL.Derivation.axiom (Peano.Axiom.mul_succ (succ q) w)
    have h₂ := swap_successor_tail (mul q w) w q
    have h₃ := FOL.Derivation.mp
      (add_left_congr (succ w) (add (mul q w) q) (mul q (succ w)))
      (FOL.Derivation.eqSymm (.axiom (.mul_succ q w)))
    have hh : FormulaProves
        (φ.imp ((mul (succ q) (succ w)).equal (add (mul q (succ w)) (succ w)))) := by
      apply FOL.Context.closeEmpty
      apply FOL.Context.deduction
      have hmid : FOL.Context Peano.Axiom [φ]
          ((add (mul (succ q) w) (succ q)).equal (add (add (mul q w) w) (succ q))) :=
        .mp (.closed (add_left_congr (succ q) _ _)) (FOL.Context.head [] φ)
      exact FOL.Context.eqTrans (FOL.Context.eqTrans (FOL.Context.eqTrans
        (.closed h₁) hmid) (.closed h₂)) (.closed h₃)
    simpa only [FOL.substAt, φ, w, FOL.equality_subst, add_subst, succ_subst,
      mul_subst, FirstOrder.Language.Term.subst, ↓reduceIte,
      FOL.term_subst_fresh q i (succ (.var i)) hi] using hh
  have hall : FormulaProves (FOL.allAt i φ) :=
    .mp (.mp (.axiom (.induction φ i)) hbase) (.generalize i hstep)
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim φ i m)) hall
  simpa only [FOL.substAt, φ, w, FOL.equality_subst, add_subst, succ_subst,
    mul_subst, FirstOrder.Language.Term.subst, ↓reduceIte,
    FOL.term_subst_fresh q i m hi] using h

private theorem less_input : CompactArithmetic.less (.var 0) (.var 1) =
    CompactArithmetic.exAt 5 ((add (.var 0) (succ (.var 5))).equal (.var 1)) := by
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

private theorem less_output :
    CompactArithmetic.less (add (.var 2) (.var 0)) (add (.var 2) (.var 1)) =
      CompactArithmetic.exAt 6
        ((add (add (.var 2) (.var 0)) (succ (.var 6))).equal (add (.var 2) (.var 1))) := by
  simp [CompactArithmetic.less, CompactArithmetic.lessTemplate, CompactArithmetic.exAt,
    CompactArithmetic.v, FOL.allAt, Peano.add, Peano.succ,
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
      · dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]
        congr 1
        funext j
        fin_cases j <;> rfl
      · dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]
        congr 1
        funext j
        fin_cases j
        rfl
    · congr 1
      funext i
      fin_cases i <;> rfl
  · rfl

/-- A common additive prefix preserves strict order on the displayed three
free variables, with an explicit transformed order witness. -/
theorem less_add_left_vars :
    FormulaProves ((CompactArithmetic.less (.var 0) (.var 1)).imp
      (CompactArithmetic.less (add (.var 2) (.var 0)) (add (.var 2) (.var 1)))) := by
  let A : Peano.Term := .var 0
  let B : Peano.Term := .var 1
  let C : Peano.Term := .var 2
  let D : Peano.Term := .var 5
  let input : Peano.Formula := (add A (succ D)).equal B
  let output : Peano.Formula := (add (add C A) (succ (.var 6))).equal (add C B)
  let goal : Peano.Formula := CompactArithmetic.less (add C A) (add C B)
  have hw : FormulaProves (input.imp goal) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    have he : FOL.Context Peano.Axiom [input]
        ((add (add C A) (succ D)).equal (add C B)) :=
      FOL.Context.eqTrans (.closed (add_assoc C A (succ D)))
        (.mp (.closed (add_right_congr C _ _)) (FOL.Context.head [] input))
    have hs : FOL.substAt output 6 D = (add (add C A) (succ D)).equal (add C B) := by
      simp [FOL.substAt, output, A, B, C, D, FOL.equality_subst, add_subst, succ_subst,
        FirstOrder.Language.Term.subst]
    have hex : FOL.Context Peano.Axiom [input] (FOL.existsAt 6 output) := by
      apply FOL.Context.mp (.closed (FOL.Derivation.existsIntro output 6 D))
      rw [hs]
      exact he
    change FOL.Context Peano.Axiom [input]
      (CompactArithmetic.less (add (.var 2) (.var 0)) (add (.var 2) (.var 1)))
    rw [less_output]
    exact hex
  have hfresh : 5 ∉ goal.freeVarFinset := by decide
  have h := PeanoBitPositionReduction.exists_elim 5 hfresh hw
  simpa only [A, B, C, D, input, goal, less_input,
    CompactArithmetic.exAt, FOL.existsAt] using h

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := by rfl

private def shiftedOrder (a b c : Peano.Term) : Peano.Formula :=
  (CompactArithmetic.less a b).imp (CompactArithmetic.less (add c a) (add c b))

private theorem specialize (a b c : Peano.Term) (name : Nat) (t : Peano.Term)
    (h : FormulaProves (shiftedOrder a b c)) : FormulaProves (shiftedOrder
      (a.subst (fun y => if y = name then t else .var y))
      (b.subst (fun y => if y = name then t else .var y))
      (c.subst (fun y => if y = name then t else .var y))) := by
  have h₁ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim (shiftedOrder a b c) name t))
    (.generalize name h)
  simpa only [FOL.substAt, shiftedOrder, subst_imp, CompactArithmetic.less_subst, add_subst] using h₁

/-- PA proves that adding any common left term preserves the literal strict
order, even when the three terms share free variables. -/
theorem less_add_left (a b c : Peano.Term) : FormulaProves
    ((CompactArithmetic.less a b).imp (CompactArithmetic.less (add c a) (add c b))) := by
  let support := a.varFinset ∪ b.varFinset ∪ c.varFinset
  let m := support.sup id + 3
  have hm : 3 ≤ m := by dsimp [m]; omega
  have fresh (n : Nat) (hn : m ≤ n) : n ∉ support := by
    intro h
    have hle : n ≤ support.sup id := Finset.le_sup (f := id) h
    dsimp [m] at hn
    omega
  have fa (n : Nat) (hn : m ≤ n) : n ∉ a.varFinset := by
    intro h; apply fresh n hn; simp [support, h]
  have fb (n : Nat) (hn : m ≤ n) : n ∉ b.varFinset := by
    intro h; apply fresh n hn; simp [support, h]
  have h1 := specialize _ _ _ 0 (.var m) less_add_left_vars
  have h1' : FormulaProves (shiftedOrder (.var m) (.var 1) (.var 2)) := by
    simpa [FirstOrder.Language.Term.subst] using h1
  have h2 := specialize _ _ _ 1 (.var (m+1)) h1'
  have h2' : FormulaProves (shiftedOrder (.var m) (.var (m+1)) (.var 2)) := by
    simpa [FirstOrder.Language.Term.subst, show m ≠ 1 by omega] using h2
  have h3 := specialize _ _ _ 2 (.var (m+2)) h2'
  have h3' : FormulaProves (shiftedOrder (.var m) (.var (m+1)) (.var (m+2))) := by
    simpa [FirstOrder.Language.Term.subst, show m ≠ 2 by omega,
      show m+1 ≠ 2 by omega] using h3
  have h4 := specialize _ _ _ m a h3'
  have h4' : FormulaProves (shiftedOrder a (.var (m+1)) (.var (m+2))) := by
    simpa [FirstOrder.Language.Term.subst, show m+1 ≠ m by omega,
      show m+2 ≠ m by omega] using h4
  have h5 := specialize _ _ _ (m+1) b h4'
  have h5' : FormulaProves (shiftedOrder a b (.var (m+2))) := by
    simpa [FirstOrder.Language.Term.subst, FOL.term_subst_fresh a (m+1) b (fa _ (by omega)),
      show m+2 ≠ m+1 by omega] using h5
  have h6 := specialize _ _ _ (m+2) c h5'
  simpa [shiftedOrder, FirstOrder.Language.Term.subst,
    FOL.term_subst_fresh a (m+2) c (fa _ (by omega)),
    FOL.term_subst_fresh b (m+2) c (fb _ (by omega))] using h6

/-- An equality on the right argument transports the actual compact order. -/
theorem less_right_congr (left u v : Peano.Term) :
    FormulaProves ((u.equal v).imp
      ((CompactArithmetic.less left u).imp (CompactArithmetic.less left v))) := by
  obtain ⟨i, hi⟩ := FOL.fresh_for_term left
  let φ : Peano.Formula := CompactArithmetic.less left (.var i)
  have h₀ : FOL.substAt φ i u = CompactArithmetic.less left u := by
    simp only [FOL.substAt, φ, CompactArithmetic.less_subst, FirstOrder.Language.Term.subst,
      ↓reduceIte, FOL.term_subst_fresh left i u hi]
  have h₁ : FOL.substAt φ i v = CompactArithmetic.less left v := by
    simp only [FOL.substAt, φ, CompactArithmetic.less_subst, FirstOrder.Language.Term.subst,
      ↓reduceIte, FOL.term_subst_fresh left i v hi]
  have h := FOL.Derivation.logical (Axiom := Peano.Axiom)
    (FOL.LogicalAxiom.eqSubst φ i u v)
  rw [h₀, h₁] at h
  exact h

/-- A remainder below the modulus puts the corresponding quotient/remainder
sum strictly below the next quotient's product, for arbitrary terms. This is
the actual PA order formula, with no positivity or semantic premise. -/
theorem adjacent_quotient_bound (q m r : Peano.Term) :
    FormulaProves ((CompactArithmetic.less r m).imp
      (CompactArithmetic.less (add (mul q m) r) (mul (succ q) m))) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have h : FOL.Context Peano.Axiom [CompactArithmetic.less r m]
      (CompactArithmetic.less (add (mul q m) r) (add (mul q m) m)) :=
    .mp (.closed (less_add_left r m (mul q m))) (FOL.Context.head [] _)
  exact .mp (.mp (.closed (less_right_congr (add (mul q m) r)
    (add (mul q m) m) (mul (succ q) m)))
      (.closed (FOL.Derivation.eqSymm (mul_succ_left q m)))) h

end PASoundness.PeanoMultiplyQuotientStep
