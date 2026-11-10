import PASoundness.PeanoQuotientGap

/-! Uniqueness of literal beta outputs in the genuine PA proof calculus. -/
namespace PASoundness.PeanoBetaUnique
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic

private theorem beta_first_syntax :
    beta (.var 0) (.var 1) (.var 2) (.var 3) =
      FOL.existsAt 4
        (((.var 0 : Peano.Term).equal
          (add (mul (.var 4) (modulus (.var 1) (.var 2))) (.var 3))) ⊓
          (less (.var 3) (modulus (.var 1) (.var 2)))) := by
  have he : beta (.var 0) (.var 1) (.var 2) (.var 3) = betaTemplate := by
    unfold beta
    calc
      betaTemplate.subst (fun x => match x with
        | 0 => .var 0 | 1 => .var 1 | 2 => .var 2 | 3 => .var 3 | _ => zero) =
          betaTemplate.subst Term.var := by
        apply SyntaxTransport.formula_subst_agree
        intro x hx
        simp only [betaTemplate_freeVars, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> rfl
      _ = betaTemplate := SyntaxTransport.formula_subst_var _
  rw [he]
  rfl

private theorem beta_second_syntax :
    beta (.var 0) (.var 1) (.var 2) (.var 5) =
      FOL.existsAt 6
        (((.var 0 : Peano.Term).equal
          (add (mul (.var 6) (modulus (.var 1) (.var 2))) (.var 5))) ⊓
          (less (.var 5) (modulus (.var 1) (.var 2)))) := by
  simp [beta, betaTemplate, CompactArithmetic.exAt,
    CompactArithmetic.less, CompactArithmetic.lessTemplate, modulus, v,
    FOL.existsAt, FOL.allAt, Peano.add, Peano.mul, Peano.succ, Peano.zero,
    FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
    FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
    FirstOrder.Language.BoundedFormula.relabelAux, Min.min]
  repeat' first
    | rfl
    | constructor
    | (congr 1; funext i; fin_cases i <;>
        dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])
  congr 1
  funext i
  fin_cases i
  congr 1
  funext j
  fin_cases j
  · dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]
    congr 1
    funext k
    fin_cases k
    rfl
  · rfl

/-- The exact literal beta formulas have a unique remainder on the displayed
free variables. The two quotient witnesses are 4 and 6, and their respective
eigenvariable side conditions are proved from syntax. -/
theorem beta_unique_vars :
    FormulaProves ((beta (.var 0) (.var 1) (.var 2) (.var 3)).imp
      ((beta (.var 0) (.var 1) (.var 2) (.var 5)).imp
        ((.var 3 : Peano.Term).equal (.var 5)))) := by
  let B : Peano.Term := .var 0
  let C : Peano.Term := .var 1
  let I : Peano.Term := .var 2
  let R : Peano.Term := .var 3
  let S : Peano.Term := .var 5
  let Q : Peano.Term := .var 4
  let Q' : Peano.Term := .var 6
  let M : Peano.Term := modulus C I
  let first : Peano.Formula := (B.equal (add (mul Q M) R)) ⊓ (less R M)
  let second : Peano.Formula := (B.equal (add (mul Q' M) S)) ⊓ (less S M)
  let goal : Peano.Formula := R.equal S
  have hrows : FormulaProves (second.imp (first.imp goal)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    have hfirst : FOL.Context Peano.Axiom [first, second] first := FOL.Context.head _ _
    have hsecond : FOL.Context Peano.Axiom [first, second] second :=
      FOL.Context.under (FOL.Context.head [] second) first
    have hb₁ : FOL.Context Peano.Axiom [first, second] (less R M) :=
      FOL.Context.conjunctionRight hfirst
    have hb₂ : FOL.Context Peano.Axiom [first, second] (less S M) :=
      FOL.Context.conjunctionRight hsecond
    have he₁ : FOL.Context Peano.Axiom [first, second] (B.equal (add (mul Q M) R)) :=
      FOL.Context.conjunctionLeft hfirst
    have he₂ : FOL.Context Peano.Axiom [first, second] (B.equal (add (mul Q' M) S)) :=
      FOL.Context.conjunctionLeft hsecond
    have hunique : FOL.Context Peano.Axiom [first, second] ((Q.equal Q') ⊓ goal) :=
      .mp (.mp (.mp (.mp (.closed (PeanoQuotientGap.quotient_remainder_unique B Q Q' M R S))
        hb₁) hb₂) he₁) he₂
    exact FOL.Context.conjunctionRight hunique
  have hfresh6 : 6 ∉ (first.imp goal).freeVarFinset := by decide
  have he6 := PeanoBitPositionReduction.exists_elim 6 hfresh6 hrows
  have hswap : FormulaProves (first.imp ((FOL.existsAt 6 second).imp goal)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    exact .mp (.mp (.closed he6) (FOL.Context.head [first] _))
      (FOL.Context.under (FOL.Context.head [] first) _)
  have hfresh4 : 4 ∉ ((FOL.existsAt 6 second).imp goal).freeVarFinset := by decide
  have he4 := PeanoBitPositionReduction.exists_elim 4 hfresh4 hswap
  simpa only [B, C, I, R, S, Q, Q', M, first, second, goal,
    beta_first_syntax, beta_second_syntax] using he4

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := by rfl

private def uniqueRelation (b c i r s : Peano.Term) : Peano.Formula :=
  (beta b c i r).imp ((beta b c i s).imp (r.equal s))

private theorem specialize (b c i r s : Peano.Term) (name : Nat) (t : Peano.Term)
    (h : FormulaProves (uniqueRelation b c i r s)) : FormulaProves (uniqueRelation
      (b.subst (fun y => if y = name then t else .var y))
      (c.subst (fun y => if y = name then t else .var y))
      (i.subst (fun y => if y = name then t else .var y))
      (r.subst (fun y => if y = name then t else .var y))
      (s.subst (fun y => if y = name then t else .var y))) := by
  have h₁ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim (uniqueRelation b c i r s) name t))
    (.generalize name h)
  simpa only [FOL.substAt, uniqueRelation, subst_imp, beta_subst, FOL.equality_subst] using h₁

/-- PA proves uniqueness of the actual beta output for arbitrary arithmetic
terms and assignments, including terms with shared free variables. This is a
finite object-level proof transformation, not metatheoretic beta uniqueness. -/
theorem beta_unique (b c i r s : Peano.Term) :
    FormulaProves ((beta b c i r).imp ((beta b c i s).imp (r.equal s))) := by
  let support := b.varFinset ∪ c.varFinset ∪ i.varFinset ∪ r.varFinset ∪ s.varFinset
  let k := support.sup id + 6
  have hk : 6 ≤ k := by dsimp [k]; omega
  have fresh (n : Nat) (hn : k ≤ n) : n ∉ support := by
    intro h
    have hle : n ≤ support.sup id := Finset.le_sup (f := id) h
    dsimp [k] at hn
    omega
  have fb (n : Nat) (hn : k ≤ n) : n ∉ b.varFinset := by
    intro h; apply fresh n hn; simp [support, h]
  have fc (n : Nat) (hn : k ≤ n) : n ∉ c.varFinset := by
    intro h; apply fresh n hn; simp [support, h]
  have fi (n : Nat) (hn : k ≤ n) : n ∉ i.varFinset := by
    intro h; apply fresh n hn; simp [support, h]
  have fr (n : Nat) (hn : k ≤ n) : n ∉ r.varFinset := by
    intro h; apply fresh n hn; simp [support, h]
  have h1 := specialize _ _ _ _ _ 0 (.var k) beta_unique_vars
  have h1' : FormulaProves (uniqueRelation (.var k) (.var 1) (.var 2) (.var 3) (.var 5)) := by
    simpa [FirstOrder.Language.Term.subst] using h1
  have h2 := specialize _ _ _ _ _ 1 (.var (k+1)) h1'
  have h2' : FormulaProves (uniqueRelation (.var k) (.var (k+1)) (.var 2) (.var 3) (.var 5)) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 1 by omega] using h2
  have h3 := specialize _ _ _ _ _ 2 (.var (k+2)) h2'
  have h3' : FormulaProves (uniqueRelation (.var k) (.var (k+1)) (.var (k+2)) (.var 3) (.var 5)) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 2 by omega,
      show k+1 ≠ 2 by omega] using h3
  have h4 := specialize _ _ _ _ _ 3 (.var (k+3)) h3'
  have h4' : FormulaProves (uniqueRelation (.var k) (.var (k+1)) (.var (k+2)) (.var (k+3)) (.var 5)) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 3 by omega,
      show k+1 ≠ 3 by omega, show k+2 ≠ 3 by omega] using h4
  have h5 := specialize _ _ _ _ _ 5 (.var (k+4)) h4'
  have h5' : FormulaProves (uniqueRelation (.var k) (.var (k+1)) (.var (k+2)) (.var (k+3)) (.var (k+4))) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 5 by omega,
      show k+1 ≠ 5 by omega, show k+2 ≠ 5 by omega, show k+3 ≠ 5 by omega] using h5
  have h6 := specialize _ _ _ _ _ k b h5'
  have h6' : FormulaProves (uniqueRelation b (.var (k+1)) (.var (k+2)) (.var (k+3)) (.var (k+4))) := by
    simpa [FirstOrder.Language.Term.subst, show k+1 ≠ k by omega,
      show k+2 ≠ k by omega, show k+3 ≠ k by omega, show k+4 ≠ k by omega] using h6
  have h7 := specialize _ _ _ _ _ (k+1) c h6'
  have h7' : FormulaProves (uniqueRelation b c (.var (k+2)) (.var (k+3)) (.var (k+4))) := by
    simpa [FirstOrder.Language.Term.subst, FOL.term_subst_fresh b (k+1) c (fb _ (by omega)),
      show k+2 ≠ k+1 by omega, show k+3 ≠ k+1 by omega, show k+4 ≠ k+1 by omega] using h7
  have h8 := specialize _ _ _ _ _ (k+2) i h7'
  have h8' : FormulaProves (uniqueRelation b c i (.var (k+3)) (.var (k+4))) := by
    simpa [FirstOrder.Language.Term.subst, FOL.term_subst_fresh b (k+2) i (fb _ (by omega)),
      FOL.term_subst_fresh c (k+2) i (fc _ (by omega)),
      show k+3 ≠ k+2 by omega, show k+4 ≠ k+2 by omega] using h8
  have h9 := specialize _ _ _ _ _ (k+3) r h8'
  have h9' : FormulaProves (uniqueRelation b c i r (.var (k+4))) := by
    simpa [FirstOrder.Language.Term.subst, FOL.term_subst_fresh b (k+3) r (fb _ (by omega)),
      FOL.term_subst_fresh c (k+3) r (fc _ (by omega)),
      FOL.term_subst_fresh i (k+3) r (fi _ (by omega)), show k+4 ≠ k+3 by omega] using h9
  have h10 := specialize _ _ _ _ _ (k+4) s h9'
  simpa [uniqueRelation, FirstOrder.Language.Term.subst,
    FOL.term_subst_fresh b (k+4) s (fb _ (by omega)),
    FOL.term_subst_fresh c (k+4) s (fc _ (by omega)),
    FOL.term_subst_fresh i (k+4) s (fi _ (by omega)),
    FOL.term_subst_fresh r (k+4) s (fr _ (by omega))] using h10

end PASoundness.PeanoBetaUnique
