import PASoundness.PeanoBetaCRTBase

/-! Existential packaging of the zero-prefix beta CRT base. The row relation
retains its parameters under the explicit freshness requirements. No induction
step, bounded CRT or beta-trace existence is asserted. -/
namespace PASoundness.PeanoBetaCRTBaseExists
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic PeanoDivisibility
open PeanoBetaCRTBase

/-- The same-witness row and old-factor clauses for free code B=name 9 and
product P=name 10. Names 2,3 are the row index and value binders. -/
def rowClause (φ : Peano.Formula) : Peano.Formula :=
  FOL.allAt 2 ((less (.var 2) zero).imp
    (FOL.existsAt 3 (φ ⊓ beta (.var 9) (.var 1) (.var 2) (.var 3))))

def divisorClause : Peano.Formula := FOL.allAt 2
  ((less (.var 2) zero).imp (divides (modulus (.var 1) (.var 2)) (.var 10)))

/-- Inverse certificates for the free product P against all future moduli. -/
def futureClause : Peano.Formula := FOL.allAt 2 (FOL.existsAt 3 (FOL.existsAt 4
  ((mul (.var 10) (.var 3)).equal
    (add (succ zero) (mul (.var 4) (modulus (.var 1) (.var 2)))))))

/-- The matrix records explicitly that B=0 and P=1, followed by the three
literal base invariant clauses. -/
def baseMatrix (φ : Peano.Formula) : Peano.Formula :=
  (((.var 9 : Peano.Term).equal zero) ⊓ ((.var 10 : Peano.Term).equal (succ zero))) ⊓
    ((rowClause φ ⊓ divisorClause) ⊓ futureClause)

def baseExists (φ : Peano.Formula) : Peano.Formula :=
  FOL.existsAt 10 (FOL.existsAt 9 (baseMatrix φ))

private theorem row_any (φ : Peano.Formula) : FormulaProves (rowClause φ) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.generalize 2
  · intro ψ hψ
    simp at hψ
  apply FOL.Context.deduction
  exact FOL.Context.explode _
    (.mp (.closed (PeanoEmptyBitSet.no_less_zero (.var 2))) (FOL.Context.head [] _))

private theorem divisor_any : FormulaProves divisorClause := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.generalize 2
  · intro ψ hψ
    simp at hψ
  apply FOL.Context.deduction
  exact FOL.Context.explode _
    (.mp (.closed (PeanoEmptyBitSet.no_less_zero (.var 2))) (FOL.Context.head [] _))

private theorem future_subst_one : FOL.substAt futureClause 10 (succ zero) =
    FOL.allAt 2 baseInverse := by
  simp [FOL.substAt, futureClause, baseInverse, baseInverseBody, modulus,
    FOL.existsAt, FOL.allAt, Peano.add, Peano.mul, Peano.succ, Peano.zero,
    FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
    FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
    FirstOrder.Language.BoundedFormula.relabelAux]
  repeat' first
    | rfl
    | constructor
    | (congr 1; funext i; fin_cases i <;>
        dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])

/-- PA constructs an existential base code and product, explicitly satisfying
B=0 and P=1. Names 9 and 10 must be fresh in φ, so existential binders do not
capture its free parameters; names 2 and 3 intentionally bind index and value. -/
theorem base_exists (φ : Peano.Formula)
    (_hφ9 : 9 ∉ φ.freeVarFinset) (_hφ10 : 10 ∉ φ.freeVarFinset) :
    FormulaProves (baseExists φ) := by
  let E : Peano.Formula := (.var 9 : Peano.Term).equal zero
  let F : Peano.Formula := (.var 10 : Peano.Term).equal (succ zero)
  let T : Peano.Formula := baseExists φ
  have hs := FOL.Derivation.logical (Axiom := Peano.Axiom)
    (FOL.LogicalAxiom.eqSubst futureClause 10 (succ zero) (.var 10))
  rw [future_subst_one, SyntaxTransport.substAt_self] at hs
  have hEF : FormulaProves (E.imp (F.imp T)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    have he : FOL.Context Peano.Axiom [F,E] E := FOL.Context.under (FOL.Context.head [] E) F
    have hf : FOL.Context Peano.Axiom [F,E] F := FOL.Context.head [E] F
    have hfuture : FOL.Context Peano.Axiom [F,E] futureClause :=
      .mp (.mp (.closed hs) (FOL.Context.eqSymm hf)) (.closed base_inverse_all)
    have hm : FOL.Context Peano.Axiom [F,E] (baseMatrix φ) :=
      FOL.Context.conjunctionIntro (FOL.Context.conjunctionIntro he hf)
        (FOL.Context.conjunctionIntro
          (FOL.Context.conjunctionIntro (.closed (row_any φ)) (.closed divisor_any)) hfuture)
    have hi9 : FormulaProves ((baseMatrix φ).imp (FOL.existsAt 9 (baseMatrix φ))) := by
      simpa only [SyntaxTransport.substAt_self] using
        (FOL.Derivation.existsIntro (A := Peano.Axiom) (baseMatrix φ) 9 (.var 9))
    have hi10 : FormulaProves ((FOL.existsAt 9 (baseMatrix φ)).imp T) := by
      simpa only [T, baseExists, SyntaxTransport.substAt_self] using
        (FOL.Derivation.existsIntro (A := Peano.Axiom) (FOL.existsAt 9 (baseMatrix φ)) 10 (.var 10))
    exact .mp (.closed hi10) (.mp (.closed hi9) hm)
  have h9 : 9 ∉ (F.imp T).freeVarFinset := by
    simp [T, baseExists, F, FOL.existsAt, SyntaxTransport.allAt_freeVars,
      FirstOrder.Language.BoundedFormula.freeVarFinset,
      FirstOrder.Language.Term.equal,
      FirstOrder.Language.Term.bdEqual, Peano.succ, Peano.zero]
  have hE := PeanoBitPositionReduction.exists_elim 9 h9 hEF
  have hexE : FormulaProves (FOL.existsAt 9 E) := by
    have hi := FOL.Derivation.existsIntro (A := Peano.Axiom) E 9 zero
    have he : FOL.substAt E 9 zero = zero.equal zero := by
      simp [FOL.substAt, E, FOL.equality_subst, PeanoArithmetic.zero_subst,
        FirstOrder.Language.Term.subst]
    rw [he] at hi
    exact .mp hi (.logical (.eqRefl zero))
  have hF : FormulaProves (F.imp T) := .mp hE hexE
  have h10 : 10 ∉ T.freeVarFinset := by
    simp [T, baseExists, FOL.existsAt, SyntaxTransport.allAt_freeVars,
      FirstOrder.Language.BoundedFormula.freeVarFinset]
  have h := PeanoBitPositionReduction.exists_elim 10 h10 hF
  have hexF : FormulaProves (FOL.existsAt 10 F) := by
    have hi := FOL.Derivation.existsIntro (A := Peano.Axiom) F 10 (succ zero)
    have he : FOL.substAt F 10 (succ zero) = (succ zero).equal (succ zero) := by
      simp [FOL.substAt, F, FOL.equality_subst, succ_subst,
        PeanoArithmetic.zero_subst, FirstOrder.Language.Term.subst]
    rw [he] at hi
    exact .mp hi (.logical (.eqRefl (succ zero)))
  exact .mp h hexF

end PASoundness.PeanoBetaCRTBaseExists
