import PASoundness.PeanoBetaUnique
import PASoundness.PeanoPowerGrowthStep

/-! The actual zero endpoint of the beta-coded power trace, proved inside PA. -/
namespace PASoundness.PeanoPowerZero
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic

private def traceStep : Peano.Formula :=
  FOL.allAt 4 ((less (v 4) (v 0)).imp
    (exAt 5 (exAt 6
      ((beta (v 2) (v 3) (v 4) (v 5)) ⊓
        ((beta (v 2) (v 3) (succ (v 4)) (v 6)) ⊓
          ((v 6).equal (add (v 5) (v 5))))))))

private def body : Peano.Formula :=
  (beta (v 2) (v 3) zero (succ zero)) ⊓
    ((beta (v 2) (v 3) (v 0) (v 1)) ⊓ traceStep)

private def goal : Peano.Formula := ((v 0).equal zero).imp ((v 1).equal (succ zero))

private theorem body_zero_endpoint : FormulaProves (body.imp goal) := by
  let φ : Peano.Formula := beta (v 2) (v 3) (v 7) (v 1)
  have hs₀ : FOL.substAt φ 7 (v 0) = beta (v 2) (v 3) (v 0) (v 1) := by
    simp [FOL.substAt, φ, beta_subst, v, FirstOrder.Language.Term.subst]
  have hs₁ : FOL.substAt φ 7 zero = beta (v 2) (v 3) zero (v 1) := by
    simp [FOL.substAt, φ, beta_subst, v, FirstOrder.Language.Term.subst]
  have htransport := FOL.Derivation.logical (Axiom := Peano.Axiom)
    (FOL.LogicalAxiom.eqSubst φ 7 (v 0) zero)
  rw [hs₀, hs₁] at htransport
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hbody : FOL.Context Peano.Axiom [(v 0).equal zero, body] body :=
    FOL.Context.under (FOL.Context.head [] body) ((v 0).equal zero)
  have hn : FOL.Context Peano.Axiom [(v 0).equal zero, body] ((v 0).equal zero) :=
    FOL.Context.head [body] _
  have hzero : FOL.Context Peano.Axiom [(v 0).equal zero, body]
      (beta (v 2) (v 3) zero (succ zero)) := FOL.Context.conjunctionLeft hbody
  have hend : FOL.Context Peano.Axiom [(v 0).equal zero, body]
      (beta (v 2) (v 3) (v 0) (v 1)) :=
    FOL.Context.conjunctionLeft (FOL.Context.conjunctionRight hbody)
  have hend0 : FOL.Context Peano.Axiom [(v 0).equal zero, body]
      (beta (v 2) (v 3) zero (v 1)) := .mp (.mp (.closed htransport) hn) hend
  have he : FOL.Context Peano.Axiom [(v 0).equal zero, body] ((succ zero).equal (v 1)) :=
    .mp (.mp (.closed (PeanoBetaUnique.beta_unique (v 2) (v 3) zero (succ zero) (v 1))) hzero) hend0
  exact FOL.Context.eqSymm he

/-- The zero-index endpoint follows from the actual power-template's two beta
rows, with no trace existence or semantic soundness assumption. -/
theorem template_zero_endpoint : FormulaProves (pow2Template.imp goal) := by
  have hfresh3 : 3 ∉ goal.freeVarFinset := by decide
  have h₃ := PeanoBitPositionReduction.exists_elim 3 hfresh3 body_zero_endpoint
  have hfresh2 : 2 ∉ goal.freeVarFinset := by decide
  have h₂ := PeanoBitPositionReduction.exists_elim 2 hfresh2 h₃
  simpa only [pow2Template, exAt, FOL.existsAt, body, traceStep, goal] using h₂

private theorem template_as_pow2 : pow2 (.var 0) (.var 1) = pow2Template := by
  unfold pow2
  calc
    pow2Template.subst (fun y => if y = 0 then .var 0 else if y = 1 then .var 1 else zero) =
        pow2Template.subst Term.var := by
      apply SyntaxTransport.formula_subst_agree
      intro y hy
      simp only [pow2Template_freeVars, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl <;> rfl
    _ = pow2Template := SyntaxTransport.formula_subst_var _

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := by rfl

private def endpointRelation (n p : Peano.Term) : Peano.Formula :=
  (pow2 n p).imp ((n.equal zero).imp (p.equal (succ zero)))

private theorem specialize (n p : Peano.Term) (name : Nat) (t : Peano.Term)
    (h : FormulaProves (endpointRelation n p)) : FormulaProves (endpointRelation
      (n.subst (fun y => if y = name then t else .var y))
      (p.subst (fun y => if y = name then t else .var y))) := by
  have h₁ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim (endpointRelation n p) name t))
    (.generalize name h)
  simpa only [FOL.substAt, endpointRelation, subst_imp, pow2_subst, FOL.equality_subst,
    PeanoArithmetic.zero_subst, succ_subst] using h₁

/-- A literal beta-coded power trace at index zero has endpoint one, for any
arithmetic term used as endpoint. This is a genuine finite PA derivation. -/
theorem power_zero_endpoint (p : Peano.Term) :
    FormulaProves ((pow2 zero p).imp (p.equal (succ zero))) := by
  have hv : FormulaProves (endpointRelation (.var 0) (.var 1)) := by
    simpa only [endpointRelation, template_as_pow2, goal, v] using template_zero_endpoint
  have h₁ := specialize _ _ 0 zero hv
  have h₁' : FormulaProves (endpointRelation zero (.var 1)) := by
    simpa [FirstOrder.Language.Term.subst] using h₁
  have h₂ := specialize _ _ 1 p h₁'
  have h₂' : FormulaProves (endpointRelation zero p) := by
    simpa [FirstOrder.Language.Term.subst, PeanoArithmetic.zero_subst] using h₂
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  exact .mp (.mp (.closed h₂') (FOL.Context.head [] (pow2 zero p)))
    (.closed (.logical (.eqRefl zero)))

/-- The zero-index instance of the desired power-growth bound, with the
exact compact strict-order formula and no semantic hypothesis. -/
theorem power_zero_growth (p : Peano.Term) :
    FormulaProves ((pow2 zero p).imp (less zero p)) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have he : FOL.Context Peano.Axiom [pow2 zero p] (p.equal (succ zero)) :=
    .mp (.closed (power_zero_endpoint p)) (FOL.Context.head [] _)
  exact .mp (.mp (.closed (PeanoMultiplyQuotientStep.less_right_congr zero (succ zero) p))
    (FOL.Context.eqSymm he)) (.closed PeanoPowerGrowthStep.zero_less_one)

end PASoundness.PeanoPowerZero
