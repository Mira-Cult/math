import PASoundness.PeanoPowerExistenceBase

/-! Preservation of an actual beta row under a multiple-of-modulus code update. -/
namespace PASoundness.PeanoBetaCodeExtension
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic

private theorem beta_source_syntax :
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

/-- If a beta row holds, PA proves that adding any multiple of its actual
modulus to the code preserves that row. Free variables 0,1,2,3,5 are the code,
parameter, index, remainder, and multiplier respectively. -/
theorem beta_add_modulus_multiple_vars :
    FormulaProves ((beta (.var 0) (.var 1) (.var 2) (.var 3)).imp
      (beta (add (.var 0) (mul (.var 5) (modulus (.var 1) (.var 2))))
        (.var 1) (.var 2) (.var 3))) := by
  let B : Peano.Term := .var 0
  let C : Peano.Term := .var 1
  let I : Peano.Term := .var 2
  let R : Peano.Term := .var 3
  let Q : Peano.Term := .var 4
  let T : Peano.Term := .var 5
  let M : Peano.Term := modulus C I
  let row : Peano.Formula := (B.equal (add (mul Q M) R)) ⊓ (less R M)
  let goal : Peano.Formula := beta (add B (mul T M)) C I R
  have hrow : FormulaProves (row.imp goal) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    have he : FOL.Context Peano.Axiom [row] (B.equal (add (mul Q M) R)) :=
      FOL.Context.conjunctionLeft (FOL.Context.head [] row)
    have hb : FOL.Context Peano.Axiom [row] (less R M) :=
      FOL.Context.conjunctionRight (FOL.Context.head [] row)
    have h1 : FOL.Context Peano.Axiom [row]
        ((add B (mul T M)).equal (add (add (mul Q M) R) (mul T M))) :=
      .mp (.closed (PeanoAdditionAssociative.add_left_congr (mul T M) B (add (mul Q M) R))) he
    have h2 : FormulaProves
        ((add (add (mul Q M) R) (mul T M)).equal (add (add (mul Q M) (mul T M)) R)) :=
      PeanoMultiplyQuotientStep.swap_add_tail (mul Q M) R (mul T M)
    have h3 : FormulaProves
        ((add (add (mul Q M) (mul T M)) R).equal (add (mul (add Q T) M) R)) :=
      .mp (PeanoAdditionAssociative.add_left_congr R _ _)
        (FOL.Derivation.eqSymm (PeanoQuotientGap.mul_add_left Q T M))
    have hout : FOL.Context Peano.Axiom [row]
        ((add B (mul T M)).equal (add (mul (add Q T) M) R)) :=
      FOL.Context.eqTrans (FOL.Context.eqTrans h1 (.closed h2)) (.closed h3)
    exact .mp (.mp (.closed (PeanoPowerExistenceBase.beta_intro (add B (mul T M)) C I R (add Q T))) hout) hb
  have hfresh : 4 ∉ goal.freeVarFinset := by decide
  have h := PeanoBitPositionReduction.exists_elim 4 hfresh hrow
  simpa only [B, C, I, R, Q, T, M, row, goal, beta_source_syntax] using h

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := by rfl

private def extensionRelation (b c i r s : Peano.Term) : Peano.Formula :=
  (beta b c i r).imp (beta (add b (mul s (modulus c i))) c i r)

private theorem specialize (b c i r s : Peano.Term) (name : Nat) (t : Peano.Term)
    (h : FormulaProves (extensionRelation b c i r s)) : FormulaProves (extensionRelation
      (b.subst (fun y => if y = name then t else .var y))
      (c.subst (fun y => if y = name then t else .var y))
      (i.subst (fun y => if y = name then t else .var y))
      (r.subst (fun y => if y = name then t else .var y))
      (s.subst (fun y => if y = name then t else .var y))) := by
  have h₁ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim (extensionRelation b c i r s) name t))
    (.generalize name h)
  simpa only [FOL.substAt, extensionRelation, subst_imp, beta_subst, add_subst, mul_subst, modulus, succ_subst] using h₁

/-- The same row-preservation construction for arbitrary terms, including
terms sharing free variables; all quotient-witness capture is handled syntactically. -/
theorem beta_add_modulus_multiple (b c i r s : Peano.Term) :
    FormulaProves ((beta b c i r).imp (beta (add b (mul s (modulus c i))) c i r)) := by
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
  have h1 := specialize _ _ _ _ _ 0 (.var k) beta_add_modulus_multiple_vars
  have h1' : FormulaProves (extensionRelation (.var k) (.var 1) (.var 2) (.var 3) (.var 5)) := by
    simpa [FirstOrder.Language.Term.subst] using h1
  have h2 := specialize _ _ _ _ _ 1 (.var (k+1)) h1'
  have h2' : FormulaProves (extensionRelation (.var k) (.var (k+1)) (.var 2) (.var 3) (.var 5)) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 1 by omega] using h2
  have h3 := specialize _ _ _ _ _ 2 (.var (k+2)) h2'
  have h3' : FormulaProves (extensionRelation (.var k) (.var (k+1)) (.var (k+2)) (.var 3) (.var 5)) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 2 by omega,
      show k+1 ≠ 2 by omega] using h3
  have h4 := specialize _ _ _ _ _ 3 (.var (k+3)) h3'
  have h4' : FormulaProves (extensionRelation (.var k) (.var (k+1)) (.var (k+2)) (.var (k+3)) (.var 5)) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 3 by omega,
      show k+1 ≠ 3 by omega, show k+2 ≠ 3 by omega] using h4
  have h5 := specialize _ _ _ _ _ 5 (.var (k+4)) h4'
  have h5' : FormulaProves (extensionRelation (.var k) (.var (k+1)) (.var (k+2)) (.var (k+3)) (.var (k+4))) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 5 by omega,
      show k+1 ≠ 5 by omega, show k+2 ≠ 5 by omega, show k+3 ≠ 5 by omega] using h5
  have h6 := specialize _ _ _ _ _ k b h5'
  have h6' : FormulaProves (extensionRelation b (.var (k+1)) (.var (k+2)) (.var (k+3)) (.var (k+4))) := by
    simpa [FirstOrder.Language.Term.subst, show k+1 ≠ k by omega,
      show k+2 ≠ k by omega, show k+3 ≠ k by omega, show k+4 ≠ k by omega] using h6
  have h7 := specialize _ _ _ _ _ (k+1) c h6'
  have h7' : FormulaProves (extensionRelation b c (.var (k+2)) (.var (k+3)) (.var (k+4))) := by
    simpa [FirstOrder.Language.Term.subst, FOL.term_subst_fresh b (k+1) c (fb _ (by omega)),
      show k+2 ≠ k+1 by omega, show k+3 ≠ k+1 by omega, show k+4 ≠ k+1 by omega] using h7
  have h8 := specialize _ _ _ _ _ (k+2) i h7'
  have h8' : FormulaProves (extensionRelation b c i (.var (k+3)) (.var (k+4))) := by
    simpa [FirstOrder.Language.Term.subst, FOL.term_subst_fresh b (k+2) i (fb _ (by omega)),
      FOL.term_subst_fresh c (k+2) i (fc _ (by omega)),
      show k+3 ≠ k+2 by omega, show k+4 ≠ k+2 by omega] using h8
  have h9 := specialize _ _ _ _ _ (k+3) r h8'
  have h9' : FormulaProves (extensionRelation b c i r (.var (k+4))) := by
    simpa [FirstOrder.Language.Term.subst, FOL.term_subst_fresh b (k+3) r (fb _ (by omega)),
      FOL.term_subst_fresh c (k+3) r (fc _ (by omega)),
      FOL.term_subst_fresh i (k+3) r (fi _ (by omega)), show k+4 ≠ k+3 by omega] using h9
  have h10 := specialize _ _ _ _ _ (k+4) s h9'
  simpa [extensionRelation, FirstOrder.Language.Term.subst,
    FOL.term_subst_fresh b (k+4) s (fb _ (by omega)),
    FOL.term_subst_fresh c (k+4) s (fc _ (by omega)),
    FOL.term_subst_fresh i (k+4) s (fi _ (by omega)),
    FOL.term_subst_fresh r (k+4) s (fr _ (by omega))] using h10


end PASoundness.PeanoBetaCodeExtension
