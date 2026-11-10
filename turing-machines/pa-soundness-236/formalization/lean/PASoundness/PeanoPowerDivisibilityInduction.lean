import PASoundness.PeanoDivisibility
import PASoundness.PeanoBetaCRTPrefixSubst

/-! The PA induction interface for divisibility between two power traces. -/
namespace PASoundness.PeanoPowerDivisibilityInduction
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic PeanoDivisibility

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := rfl

private theorem divides_subst (k d : Peano.Term) (σ : Nat → Peano.Term) :
    (divides k d).subst σ = divides (k.subst σ) (d.subst σ) := by
  unfold divides
  rw [SyntaxTransport.formula_subst_comp]
  congr 1
  funext y
  by_cases h0 : y = 0 <;> by_cases h1 : y = 1 <;> simp [h0, h1]

/-- The body uses free names 1, 2, and 6 for the smaller exponent, its power,
and the larger power, respectively. -/
def body (n : Peano.Term) : Peano.Formula :=
  (pow2 (.var 1) (.var 2)).imp ((pow2 n (.var 6)).imp
    ((less (.var 1) n).imp (divides (add (.var 2) (.var 2)) (.var 6))))

def familyAt (n : Peano.Term) : Peano.Formula :=
  FOL.allAt 1 (FOL.allAt 2 (FOL.allAt 6 (body n)))

def family : Peano.Formula := familyAt (.var 0)

theorem base_syntax : FOL.substAt family 0 zero = familyAt zero := by
  unfold family familyAt
  rw [PeanoBetaCRTPrefixSubst.Syntax.subst_zero_allAt _ 0 1 (by decide),
    PeanoBetaCRTPrefixSubst.Syntax.subst_zero_allAt _ 0 2 (by decide),
    PeanoBetaCRTPrefixSubst.Syntax.subst_zero_allAt _ 0 6 (by decide)]
  simp [FOL.substAt, body, subst_imp, pow2_subst, less_subst, divides_subst,
    add_subst, FirstOrder.Language.Term.subst]

theorem successor_syntax : FOL.substAt family 0 (succ (.var 0)) =
    familyAt (succ (.var 0)) := by
  unfold family familyAt
  rw [PeanoBetaCRTPrefixSubst.Syntax.subst_succSelf_allAt _ 0 1 (by decide),
    PeanoBetaCRTPrefixSubst.Syntax.subst_succSelf_allAt _ 0 2 (by decide),
    PeanoBetaCRTPrefixSubst.Syntax.subst_succSelf_allAt _ 0 6 (by decide)]
  simp [FOL.substAt, body, subst_imp, pow2_subst, less_subst, divides_subst,
    add_subst, FirstOrder.Language.Term.subst]

/-- Actual PA induction, conditional on separately supplied PA derivations
of the base and successor implications. This theorem does not assert either
premise or the unqualified divisibility result. -/
theorem family_of_base_and_step (hbase : FormulaProves (familyAt zero))
    (hstep : FormulaProves (family.imp (familyAt (succ (.var 0))))) :
    FormulaProves (FOL.allAt 0 family) := by
  have hb : FormulaProves (FOL.substAt family 0 zero) := by
    rw [base_syntax]; exact hbase
  have hs : FormulaProves (family.imp (FOL.substAt family 0 (succ (.var 0)))) := by
    rw [successor_syntax]; exact hstep
  exact .mp (.mp (.axiom (.induction family 0)) hb) (.generalize 0 hs)

/-- Eliminate the quantified exponents and outputs at their own free names.
The same two PA derivations remain explicit premises. -/
theorem body_of_base_and_step (hbase : FormulaProves (familyAt zero))
    (hstep : FormulaProves (family.imp (familyAt (succ (.var 0))))) :
    FormulaProves (body (.var 0)) := by
  have hfamily : FormulaProves family := by
    have h := FOL.Derivation.mp
      (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim family 0 (.var 0)))
      (family_of_base_and_step hbase hstep)
    simpa only [SyntaxTransport.substAt_self] using h
  apply FOL.Context.closeEmpty
  have h1 : FOL.Context Peano.Axiom [] (FOL.allAt 2 (FOL.allAt 6 (body (.var 0)))) :=
    FOL.Context.allSelf (.closed hfamily)
  have h2 : FOL.Context Peano.Axiom [] (FOL.allAt 6 (body (.var 0))) :=
    FOL.Context.allSelf h1
  exact FOL.Context.allSelf h2

end PASoundness.PeanoPowerDivisibilityInduction

#print axioms PASoundness.PeanoPowerDivisibilityInduction.family_of_base_and_step
#print axioms PASoundness.PeanoPowerDivisibilityInduction.body_of_base_and_step
