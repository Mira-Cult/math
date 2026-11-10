import PASoundness.PeanoMultiplyQuotientStep
import PASoundness.PeanoAdditionCancellation
import PASoundness.PeanoOrderTotality

/-! Genuine PA arithmetic towards arbitrary quotient gaps. -/
namespace PASoundness.PeanoQuotientGap
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication PeanoAdditionAssociative
open PeanoAdditionCancellation PeanoMultiplyQuotientStep

private theorem shuffle_four (a b c d : Peano.Term) :
    FormulaProves ((add (add a b) (add c d)).equal (add (add a c) (add b d))) := by
  have h₁ := FOL.Derivation.eqSymm (add_assoc (add a b) c d)
  have h₂ := FOL.Derivation.mp (add_left_congr d _ _) (swap_add_tail a b c)
  have h₃ := add_assoc (add a c) b d
  exact FOL.Derivation.eqTrans (FOL.Derivation.eqTrans h₁ h₂) h₃

/-- Left distributivity of multiplication in the genuine PA calculus, for
arbitrary arithmetic terms. -/
theorem mul_add_left (a b m : Peano.Term) :
    FormulaProves ((mul (add a b) m).equal (add (mul a m) (mul b m))) := by
  obtain ⟨i, hi⟩ := FOL.fresh_for_term (add a b)
  have hi' : i ∉ a.varFinset ∧ i ∉ b.varFinset := by
    simpa [Peano.add, FirstOrder.Language.Term.varFinset] using hi
  let w : Peano.Term := .var i
  let φ : Peano.Formula := (mul (add a b) w).equal (add (mul a w) (mul b w))
  have hbase : FormulaProves (FOL.substAt φ i zero) := by
    have h₁ := FOL.Derivation.axiom (Peano.Axiom.mul_zero (add a b))
    have h₂ := FOL.Derivation.mp (add_left_congr (mul b zero) (mul a zero) zero)
      (.axiom (.mul_zero a))
    have h₃ := FOL.Derivation.eqTrans (FOL.Derivation.eqTrans h₂ (zero_add (mul b zero)))
      (.axiom (.mul_zero b))
    have h := FOL.Derivation.eqTrans h₁ (FOL.Derivation.eqSymm h₃)
    simpa only [FOL.substAt, φ, w, FOL.equality_subst, add_subst, mul_subst,
      PeanoArithmetic.zero_subst, FirstOrder.Language.Term.subst, ↓reduceIte,
      FOL.term_subst_fresh a i zero hi'.1, FOL.term_subst_fresh b i zero hi'.2] using h
  have hstep : FormulaProves (φ.imp (FOL.substAt φ i (succ w))) := by
    have h₁ := FOL.Derivation.axiom (Peano.Axiom.mul_succ (add a b) w)
    have h₂ := shuffle_four (mul a w) (mul b w) a b
    have h₃ := FOL.Derivation.mp
      (add_left_congr (add (mul b w) b) (add (mul a w) a) (mul a (succ w)))
      (FOL.Derivation.eqSymm (.axiom (.mul_succ a w)))
    have h₄ := FOL.Derivation.mp
      (add_right_congr (mul a (succ w)) (add (mul b w) b) (mul b (succ w)))
      (FOL.Derivation.eqSymm (.axiom (.mul_succ b w)))
    have hh : FormulaProves (φ.imp
        ((mul (add a b) (succ w)).equal (add (mul a (succ w)) (mul b (succ w))))) := by
      apply FOL.Context.closeEmpty
      apply FOL.Context.deduction
      have hmid : FOL.Context Peano.Axiom [φ]
          ((add (mul (add a b) w) (add a b)).equal
            (add (add (mul a w) (mul b w)) (add a b))) :=
        .mp (.closed (add_left_congr (add a b) _ _)) (FOL.Context.head [] φ)
      exact FOL.Context.eqTrans (FOL.Context.eqTrans (FOL.Context.eqTrans
        (FOL.Context.eqTrans (.closed h₁) hmid) (.closed h₂)) (.closed h₃)) (.closed h₄)
    simpa only [FOL.substAt, φ, w, FOL.equality_subst, add_subst, succ_subst, mul_subst,
      FirstOrder.Language.Term.subst, ↓reduceIte,
      FOL.term_subst_fresh a i (succ (.var i)) hi'.1,
      FOL.term_subst_fresh b i (succ (.var i)) hi'.2] using hh
  have hall : FormulaProves (FOL.allAt i φ) :=
    .mp (.mp (.axiom (.induction φ i)) hbase) (.generalize i hstep)
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim φ i m)) hall
  simpa only [FOL.substAt, φ, w, FOL.equality_subst, add_subst, mul_subst,
    FirstOrder.Language.Term.subst, ↓reduceIte,
    FOL.term_subst_fresh a i m hi'.1, FOL.term_subst_fresh b i m hi'.2] using h

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

private theorem less_output : CompactArithmetic.less (.var 0) (add (.var 1) (.var 2)) =
    CompactArithmetic.exAt 6
      ((add (.var 0) (succ (.var 6))).equal (add (.var 1) (.var 2))) := by
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
      · rfl
      · dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]
        congr 1
        funext j
        fin_cases j
        rfl
    · congr 1
      funext i
      fin_cases i <;> rfl
  · rfl

private theorem less_add_right_vars :
    FormulaProves ((CompactArithmetic.less (.var 0) (.var 1)).imp
      (CompactArithmetic.less (.var 0) (add (.var 1) (.var 2)))) := by
  let A : Peano.Term := .var 0
  let B : Peano.Term := .var 1
  let C : Peano.Term := .var 2
  let D : Peano.Term := .var 5
  let input : Peano.Formula := (add A (succ D)).equal B
  let output : Peano.Formula := (add A (succ (.var 6))).equal (add B C)
  let goal : Peano.Formula := CompactArithmetic.less A (add B C)
  let witness : Peano.Term := add D C
  have hw : FormulaProves (input.imp goal) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    have h₁ : FormulaProves
        ((add A (succ witness)).equal (add A (add (succ D) C))) :=
      FOL.Derivation.mp (add_right_congr A _ _)
        (FOL.Derivation.eqSymm (add_succ_left D C))
    have h₂ : FOL.Context Peano.Axiom [input]
        ((add A (succ witness)).equal (add B C)) :=
      FOL.Context.eqTrans (FOL.Context.eqTrans (.closed h₁)
        (.closed (FOL.Derivation.eqSymm (add_assoc A (succ D) C))))
        (.mp (.closed (add_left_congr C _ _)) (FOL.Context.head [] input))
    have hs : FOL.substAt output 6 witness = (add A (succ witness)).equal (add B C) := by
      simp [FOL.substAt, output, A, B, C, FOL.equality_subst, add_subst, succ_subst,
        FirstOrder.Language.Term.subst]
    have hex : FOL.Context Peano.Axiom [input] (FOL.existsAt 6 output) := by
      apply FOL.Context.mp (.closed (FOL.Derivation.existsIntro output 6 witness))
      rw [hs]
      exact h₂
    change FOL.Context Peano.Axiom [input] (CompactArithmetic.less (.var 0) (add (.var 1) (.var 2)))
    rw [less_output]
    exact hex
  have hfresh : 5 ∉ goal.freeVarFinset := by decide
  have h := PeanoBitPositionReduction.exists_elim 5 hfresh hw
  simpa only [A, B, C, D, input, goal, less_input,
    CompactArithmetic.exAt, FOL.existsAt] using h

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := by rfl

private def weakenedOrder (a b c : Peano.Term) : Peano.Formula :=
  (CompactArithmetic.less a b).imp (CompactArithmetic.less a (add b c))

private theorem specialize (a b c : Peano.Term) (name : Nat) (t : Peano.Term)
    (h : FormulaProves (weakenedOrder a b c)) : FormulaProves (weakenedOrder
      (a.subst (fun y => if y = name then t else .var y))
      (b.subst (fun y => if y = name then t else .var y))
      (c.subst (fun y => if y = name then t else .var y))) := by
  have h₁ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim (weakenedOrder a b c) name t))
    (.generalize name h)
  simpa only [FOL.substAt, weakenedOrder, subst_imp, CompactArithmetic.less_subst, add_subst] using h₁

/-- PA proves `a<b → a<b+c` for arbitrary arithmetic terms. -/
theorem less_add_right (a b c : Peano.Term) :
    FormulaProves ((CompactArithmetic.less a b).imp (CompactArithmetic.less a (add b c))) := by
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
  have h1 := specialize _ _ _ 0 (.var m) less_add_right_vars
  have h1' : FormulaProves (weakenedOrder (.var m) (.var 1) (.var 2)) := by
    simpa [FirstOrder.Language.Term.subst] using h1
  have h2 := specialize _ _ _ 1 (.var (m+1)) h1'
  have h2' : FormulaProves (weakenedOrder (.var m) (.var (m+1)) (.var 2)) := by
    simpa [FirstOrder.Language.Term.subst, show m ≠ 1 by omega] using h2
  have h3 := specialize _ _ _ 2 (.var (m+2)) h2'
  have h3' : FormulaProves (weakenedOrder (.var m) (.var (m+1)) (.var (m+2))) := by
    simpa [FirstOrder.Language.Term.subst, show m ≠ 2 by omega,
      show m+1 ≠ 2 by omega] using h3
  have h4 := specialize _ _ _ m a h3'
  have h4' : FormulaProves (weakenedOrder a (.var (m+1)) (.var (m+2))) := by
    simpa [FirstOrder.Language.Term.subst, show m+1 ≠ m by omega,
      show m+2 ≠ m by omega] using h4
  have h5 := specialize _ _ _ (m+1) b h4'
  have h5' : FormulaProves (weakenedOrder a b (.var (m+2))) := by
    simpa [FirstOrder.Language.Term.subst, FOL.term_subst_fresh a (m+1) b (fa _ (by omega)),
      show m+2 ≠ m+1 by omega] using h5
  have h6 := specialize _ _ _ (m+2) c h5'
  simpa [weakenedOrder, FirstOrder.Language.Term.subst,
    FOL.term_subst_fresh a (m+2) c (fa _ (by omega)),
    FOL.term_subst_fresh b (m+2) c (fb _ (by omega))] using h6

/-- The arbitrary-gap inequality on four free variables. The witness for
the quotient comparison is consumed by an actual PA derivation. -/
theorem quotient_gap_vars :
    FormulaProves ((CompactArithmetic.less (.var 0) (.var 1)).imp
      ((CompactArithmetic.less (.var 3) (.var 2)).imp
        (CompactArithmetic.less (add (mul (.var 0) (.var 2)) (.var 3))
          (mul (.var 1) (.var 2))))) := by
  let Q : Peano.Term := .var 0
  let Q' : Peano.Term := .var 1
  let M : Peano.Term := .var 2
  let R : Peano.Term := .var 3
  let D : Peano.Term := .var 5
  let row : Peano.Formula := (add Q (succ D)).equal Q'
  let bound : Peano.Formula := CompactArithmetic.less R M
  let goal : Peano.Formula :=
    CompactArithmetic.less (add (mul Q M) R) (mul Q' M)
  have hw : FormulaProves (row.imp (bound.imp goal)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    have hrow : FOL.Context Peano.Axiom [bound, row] row :=
      FOL.Context.under (FOL.Context.head [] row) bound
    have hbound : FOL.Context Peano.Axiom [bound, row] bound := FOL.Context.head _ _
    have hqeq : FormulaProves ((add Q (succ D)).equal (add (succ Q) D)) :=
      FOL.Derivation.eqTrans (.axiom (.add_succ Q D))
        (FOL.Derivation.eqSymm (add_succ_left Q D))
    have hq' : FOL.Context Peano.Axiom [bound, row]
        (Q'.equal (add (succ Q) D)) :=
      FOL.Context.eqTrans (FOL.Context.eqSymm hrow) (.closed hqeq)
    have hproduct : FOL.Context Peano.Axiom [bound, row]
        ((mul Q' M).equal (add (mul (succ Q) M) (mul D M))) :=
      FOL.Context.eqTrans (.mp (.closed (mul_left_congr Q' (add (succ Q) D) M)) hq')
        (.closed (mul_add_left (succ Q) D M))
    have hfirst : FOL.Context Peano.Axiom [bound, row]
        (CompactArithmetic.less (add (mul Q M) R) (mul (succ Q) M)) :=
      .mp (.closed (adjacent_quotient_bound Q M R)) hbound
    have hsecond : FOL.Context Peano.Axiom [bound, row]
        (CompactArithmetic.less (add (mul Q M) R) (add (mul (succ Q) M) (mul D M))) :=
      .mp (.closed (less_add_right (add (mul Q M) R) (mul (succ Q) M) (mul D M))) hfirst
    exact .mp (.mp (.closed (less_right_congr (add (mul Q M) R)
      (add (mul (succ Q) M) (mul D M)) (mul Q' M))) (FOL.Context.eqSymm hproduct)) hsecond
  have hfresh : 5 ∉ (bound.imp goal).freeVarFinset := by decide
  have h := PeanoBitPositionReduction.exists_elim 5 hfresh hw
  simpa only [Q, Q', M, R, D, row, bound, goal, less_input,
    CompactArithmetic.exAt, FOL.existsAt] using h

private def gapRelation (q q' m r : Peano.Term) : Peano.Formula :=
  (CompactArithmetic.less q q').imp
    ((CompactArithmetic.less r m).imp (CompactArithmetic.less (add (mul q m) r) (mul q' m)))

private theorem specializeGap (q q' m r : Peano.Term) (name : Nat) (t : Peano.Term)
    (h : FormulaProves (gapRelation q q' m r)) : FormulaProves (gapRelation
      (q.subst (fun y => if y = name then t else .var y))
      (q'.subst (fun y => if y = name then t else .var y))
      (m.subst (fun y => if y = name then t else .var y))
      (r.subst (fun y => if y = name then t else .var y))) := by
  have h₁ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim (gapRelation q q' m r) name t))
    (.generalize name h)
  simpa only [FOL.substAt, gapRelation, subst_imp, CompactArithmetic.less_subst,
    add_subst, mul_subst] using h₁

/-- For arbitrary arithmetic terms, PA derives the exact strict
quotient-gap inequality `q<q' → r<m → q*m+r<q'*m`. The two antecedents
are genuine object-level hypotheses, not metatheoretic assumptions. -/
theorem quotient_gap (q q' m r : Peano.Term) :
    FormulaProves ((CompactArithmetic.less q q').imp
      ((CompactArithmetic.less r m).imp
        (CompactArithmetic.less (add (mul q m) r) (mul q' m)))) := by
  let support := q.varFinset ∪ q'.varFinset ∪ m.varFinset ∪ r.varFinset
  let k := support.sup id + 4
  have hk : 4 ≤ k := by dsimp [k]; omega
  have fresh (n : Nat) (hn : k ≤ n) : n ∉ support := by
    intro h
    have hle : n ≤ support.sup id := Finset.le_sup (f := id) h
    dsimp [k] at hn
    omega
  have fq (n : Nat) (hn : k ≤ n) : n ∉ q.varFinset := by
    intro h; apply fresh n hn; simp [support, h]
  have fq' (n : Nat) (hn : k ≤ n) : n ∉ q'.varFinset := by
    intro h; apply fresh n hn; simp [support, h]
  have fm (n : Nat) (hn : k ≤ n) : n ∉ m.varFinset := by
    intro h; apply fresh n hn; simp [support, h]
  have h1 := specializeGap _ _ _ _ 0 (.var k) quotient_gap_vars
  have h1' : FormulaProves (gapRelation (.var k) (.var 1) (.var 2) (.var 3)) := by
    simpa [FirstOrder.Language.Term.subst] using h1
  have h2 := specializeGap _ _ _ _ 1 (.var (k+1)) h1'
  have h2' : FormulaProves (gapRelation (.var k) (.var (k+1)) (.var 2) (.var 3)) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 1 by omega] using h2
  have h3 := specializeGap _ _ _ _ 2 (.var (k+2)) h2'
  have h3' : FormulaProves (gapRelation (.var k) (.var (k+1)) (.var (k+2)) (.var 3)) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 2 by omega,
      show k+1 ≠ 2 by omega] using h3
  have h4 := specializeGap _ _ _ _ 3 (.var (k+3)) h3'
  have h4' : FormulaProves (gapRelation (.var k) (.var (k+1)) (.var (k+2)) (.var (k+3))) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 3 by omega,
      show k+1 ≠ 3 by omega, show k+2 ≠ 3 by omega] using h4
  have h5 := specializeGap _ _ _ _ k q h4'
  have h5' : FormulaProves (gapRelation q (.var (k+1)) (.var (k+2)) (.var (k+3))) := by
    simpa [FirstOrder.Language.Term.subst, show k+1 ≠ k by omega,
      show k+2 ≠ k by omega, show k+3 ≠ k by omega] using h5
  have h6 := specializeGap _ _ _ _ (k+1) q' h5'
  have h6' : FormulaProves (gapRelation q q' (.var (k+2)) (.var (k+3))) := by
    simpa [FirstOrder.Language.Term.subst, FOL.term_subst_fresh q (k+1) q' (fq _ (by omega)),
      show k+2 ≠ k+1 by omega, show k+3 ≠ k+1 by omega] using h6
  have h7 := specializeGap _ _ _ _ (k+2) m h6'
  have h7' : FormulaProves (gapRelation q q' m (.var (k+3))) := by
    simpa [FirstOrder.Language.Term.subst, FOL.term_subst_fresh q (k+2) m (fq _ (by omega)),
      FOL.term_subst_fresh q' (k+2) m (fq' _ (by omega)), show k+3 ≠ k+2 by omega] using h7
  have h8 := specializeGap _ _ _ _ (k+3) r h7'
  simpa [gapRelation, FirstOrder.Language.Term.subst,
    FOL.term_subst_fresh q (k+3) r (fq _ (by omega)),
    FOL.term_subst_fresh q' (k+3) r (fq' _ (by omega)),
    FOL.term_subst_fresh m (k+3) r (fm _ (by omega))] using h8

/-- Adding a natural term cannot make the result strictly less than the
original term, derived from order weakening and PA irreflexivity. -/
theorem not_less_add (a c : Peano.Term) :
    FormulaProves (CompactArithmetic.less (add a c) a).not :=
  .mp (FOL.Derivation.contrapose (less_add_right (add a c) a c))
    (PeanoOrderIrreflexive.less_self (add a c))

/-- Equality on the left argument transports the literal compact order. -/
theorem less_left_congr (u v right : Peano.Term) :
    FormulaProves ((u.equal v).imp
      ((CompactArithmetic.less u right).imp (CompactArithmetic.less v right))) := by
  obtain ⟨i, hi⟩ := FOL.fresh_for_term right
  let φ : Peano.Formula := CompactArithmetic.less (.var i) right
  have h₀ : FOL.substAt φ i u = CompactArithmetic.less u right := by
    simp only [FOL.substAt, φ, CompactArithmetic.less_subst, FirstOrder.Language.Term.subst,
      ↓reduceIte, FOL.term_subst_fresh right i u hi]
  have h₁ : FOL.substAt φ i v = CompactArithmetic.less v right := by
    simp only [FOL.substAt, φ, CompactArithmetic.less_subst, FirstOrder.Language.Term.subst,
      ↓reduceIte, FOL.term_subst_fresh right i v hi]
  have h := FOL.Derivation.logical (Axiom := Peano.Axiom)
    (FOL.LogicalAxiom.eqSubst φ i u v)
  rw [h₀, h₁] at h
  exact h

/-- The different-quotient case: if `q<q'`, `r<m`, and the first quotient
row holds, PA refutes any second row with quotient `q'`, irrespective of its
remainder. All comparisons and equations are literal PA formulas. -/
theorem quotient_rows_exclude_less (b q q' m r s : Peano.Term) :
    FormulaProves ((CompactArithmetic.less q q').imp
      ((CompactArithmetic.less r m).imp
        ((b.equal (add (mul q m) r)).imp
          (b.equal (add (mul q' m) s)).not))) := by
  let ltQ : Peano.Formula := CompactArithmetic.less q q'
  let ltR : Peano.Formula := CompactArithmetic.less r m
  let eqR : Peano.Formula := b.equal (add (mul q m) r)
  let eqS : Peano.Formula := b.equal (add (mul q' m) s)
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hq : FOL.Context Peano.Axiom [eqS, eqR, ltR, ltQ] ltQ :=
    FOL.Context.under (FOL.Context.under (FOL.Context.under (FOL.Context.head [] ltQ) ltR) eqR) eqS
  have hr : FOL.Context Peano.Axiom [eqS, eqR, ltR, ltQ] ltR :=
    FOL.Context.under (FOL.Context.under (FOL.Context.head [ltQ] ltR) eqR) eqS
  have heR : FOL.Context Peano.Axiom [eqS, eqR, ltR, ltQ] eqR :=
    FOL.Context.under (FOL.Context.head [ltR, ltQ] eqR) eqS
  have heS : FOL.Context Peano.Axiom [eqS, eqR, ltR, ltQ] eqS := FOL.Context.head _ _
  have hgap : FOL.Context Peano.Axiom [eqS, eqR, ltR, ltQ]
      (CompactArithmetic.less (add (mul q m) r) (mul q' m)) :=
    .mp (.mp (.closed (quotient_gap q q' m r)) hq) hr
  have hb : FOL.Context Peano.Axiom [eqS, eqR, ltR, ltQ]
      (CompactArithmetic.less b (mul q' m)) :=
    .mp (.mp (.closed (less_left_congr (add (mul q m) r) b (mul q' m)))
      (FOL.Context.eqSymm heR)) hgap
  have hf : FOL.Context Peano.Axiom [eqS, eqR, ltR, ltQ]
      (CompactArithmetic.less (add (mul q' m) s) (mul q' m)) :=
    .mp (.mp (.closed (less_left_congr b (add (mul q' m) s) (mul q' m))) heS) hb
  exact .mp (.closed (not_less_add (mul q' m) s)) hf

private theorem or_elim {L : Language} {A : FOL.Formula L → Prop}
    {Γ : List (FOL.Formula L)} {φ ψ χ : FOL.Formula L}
    (h : FOL.Context A Γ (φ ⊔ ψ)) (hφ : FOL.Context A Γ (φ.imp χ))
    (hψ : FOL.Context A Γ (ψ.imp χ)) : FOL.Context A Γ χ := by
  apply FOL.Context.dne
  apply FOL.Context.deduction
  have hnφ : FOL.Context A (χ.not :: Γ) φ.not :=
    .mp (FOL.Context.under (FOL.Context.contrapose hφ) χ.not) (FOL.Context.head Γ χ.not)
  have hψ' : FOL.Context A (χ.not :: Γ) ψ := .mp (FOL.Context.under h χ.not) hnφ
  exact .mp (FOL.Context.head Γ χ.not) (.mp (FOL.Context.under hψ χ.not) hψ')

/-- Explicit quotient/remainder uniqueness in PA: equal dividends, the same
modulus, and both literal remainder bounds force equal quotient and remainder
terms. No semantic truth, model soundness or hidden positivity premise is used. -/
theorem quotient_remainder_unique (b q q' m r s : Peano.Term) :
    FormulaProves ((CompactArithmetic.less r m).imp
      ((CompactArithmetic.less s m).imp
        ((b.equal (add (mul q m) r)).imp
          ((b.equal (add (mul q' m) s)).imp ((q.equal q') ⊓ (r.equal s)))))) := by
  let ltR : Peano.Formula := CompactArithmetic.less r m
  let ltS : Peano.Formula := CompactArithmetic.less s m
  let eqR : Peano.Formula := b.equal (add (mul q m) r)
  let eqS : Peano.Formula := b.equal (add (mul q' m) s)
  let eqQ : Peano.Formula := q.equal q'
  let ltQ : Peano.Formula := CompactArithmetic.less q q'
  let gtQ : Peano.Formula := CompactArithmetic.less q' q
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hr : FOL.Context Peano.Axiom [eqS, eqR, ltS, ltR] ltR :=
    FOL.Context.under (FOL.Context.under (FOL.Context.under (FOL.Context.head [] ltR) ltS) eqR) eqS
  have hs : FOL.Context Peano.Axiom [eqS, eqR, ltS, ltR] ltS :=
    FOL.Context.under (FOL.Context.under (FOL.Context.head [ltR] ltS) eqR) eqS
  have hR : FOL.Context Peano.Axiom [eqS, eqR, ltS, ltR] eqR :=
    FOL.Context.under (FOL.Context.head [ltS, ltR] eqR) eqS
  have hS : FOL.Context Peano.Axiom [eqS, eqR, ltS, ltR] eqS := FOL.Context.head _ _
  have hlt : FOL.Context Peano.Axiom [eqS, eqR, ltS, ltR] (ltQ.imp eqQ) := by
    apply FOL.Context.deduction
    have hcontra : FOL.Context Peano.Axiom [ltQ, eqS, eqR, ltS, ltR] (⊥ : Peano.Formula) :=
      .mp (.mp (.mp (.mp (.closed (quotient_rows_exclude_less b q q' m r s))
        (FOL.Context.head _ ltQ)) (FOL.Context.under hr ltQ)) (FOL.Context.under hR ltQ))
        (FOL.Context.under hS ltQ)
    exact FOL.Context.explode eqQ hcontra
  have hgt : FOL.Context Peano.Axiom [eqS, eqR, ltS, ltR] (gtQ.imp eqQ) := by
    apply FOL.Context.deduction
    have hcontra : FOL.Context Peano.Axiom [gtQ, eqS, eqR, ltS, ltR] (⊥ : Peano.Formula) :=
      .mp (.mp (.mp (.mp (.closed (quotient_rows_exclude_less b q' q m s r))
        (FOL.Context.head _ gtQ)) (FOL.Context.under hs gtQ)) (FOL.Context.under hS gtQ))
        (FOL.Context.under hR gtQ)
    exact FOL.Context.explode eqQ hcontra
  have hid : FOL.Context Peano.Axiom [eqS, eqR, ltS, ltR] (eqQ.imp eqQ) :=
    .closed (.identity eqQ)
  have hinner : FOL.Context Peano.Axiom [eqS, eqR, ltS, ltR] ((eqQ ⊔ ltQ).imp eqQ) := by
    apply FOL.Context.deduction
    exact or_elim (FOL.Context.head _ (eqQ ⊔ ltQ))
      (FOL.Context.under hid _) (FOL.Context.under hlt _)
  have hq : FOL.Context Peano.Axiom [eqS, eqR, ltS, ltR] eqQ :=
    or_elim (.closed (PeanoOrderTotality.trichotomy_all q q')) hinner hgt
  have hrem : FOL.Context Peano.Axiom [eqS, eqR, ltS, ltR] (r.equal s) :=
    .mp (.mp (.mp (.closed (remainders_of_quotient_equality b q q' m r s)) hq) hR) hS
  exact FOL.Context.conjunctionIntro hq hrem

end PASoundness.PeanoQuotientGap
