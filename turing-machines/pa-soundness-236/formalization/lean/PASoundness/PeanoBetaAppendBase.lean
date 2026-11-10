import PASoundness.PeanoBetaAppendPreserve
import PASoundness.PeanoBetaCRTInvariant
import PASoundness.PeanoBetaCRTPrefixSubst

/-! Transfer the initial beta row from a supplied CRT row family.
This does not establish existence of the code or a doubling trace. -/
namespace PASoundness.PeanoBetaAppendBase
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoBetaAppendRelation PeanoBetaCRTInvariant

private theorem subst_not (φ : Peano.Formula) (σ : Nat → Peano.Term) :
    φ.not.subst σ = (φ.subst σ).not := by
  simp [FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.mapTermRel]
  rfl

private theorem subst_and (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ ⊓ ψ).subst σ = (φ.subst σ) ⊓ (ψ.subst σ) := by
  change (φ.imp ψ.not).not.subst σ = ((φ.subst σ).imp (ψ.subst σ).not).not
  rw [subst_not, show (φ.imp ψ.not).subst σ = (φ.subst σ).imp (ψ.not.subst σ) from rfl, subst_not]

private theorem subst_or (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ ⊔ ψ).subst σ = (φ.subst σ) ⊔ (ψ.subst σ) := by
  change (φ.not.imp ψ).subst σ = ((φ.subst σ).not.imp (ψ.subst σ))
  rw [show (φ.not.imp ψ).subst σ = (φ.not.subst σ).imp (ψ.subst σ) from rfl, subst_not]

def baseRelation : Peano.Formula :=
  (less zero (succ (.var 0)) ⊓ beta (.var 4) (.var 5) zero (.var 3)) ⊔
  ((zero.equal (succ (.var 0))) ⊓
    ((.var 3 : Peano.Term).equal (add (.var 6) (.var 6))))

private theorem row_instance_syntax : FOL.substAt
    ((less (.var 2) (succ (succ (.var 0)))).imp
      (FOL.existsAt 3 (appendRelation ⊓ beta (.var 9) (.var 1) (.var 2) (.var 3))))
    2 zero = ((less zero (succ (succ (.var 0)))).imp
      (FOL.existsAt 3 (baseRelation ⊓ beta (.var 9) (.var 1) zero (.var 3)))) := by
  change (FOL.substAt (less (.var 2) (succ (succ (.var 0)))) 2 zero).imp
      (FOL.substAt (FOL.existsAt 3 (appendRelation ⊓ beta (.var 9) (.var 1) (.var 2) (.var 3))) 2 zero) = _
  rw [PeanoBetaCRTPrefixSubst.Syntax.subst_zero_existsAt _ 2 3 (by decide)]
  simp [FOL.substAt, subst_and, subst_or, appendRelation, baseRelation,
    beta_subst, less_subst, FOL.equality_subst, add_subst,
    succ_subst, FirstOrder.Language.Term.subst]

/-- Given a recoded row family and the original initial row, PA derives the
same initial row for the new beta code and parameter. -/
theorem initial_row_preserved : FormulaProves
    ((rowsAt appendRelation (succ (succ (.var 0))) 9).imp
      ((beta (.var 4) (.var 5) zero (succ zero)).imp
        (beta (.var 9) (.var 1) zero (succ zero)))) := by
  let O := beta (.var 4) (.var 5) zero (.var 3)
  let N := beta (.var 9) (.var 1) zero (.var 3)
  let O₁ := beta (.var 4) (.var 5) zero (succ zero)
  let N₁ := beta (.var 9) (.var 1) zero (succ zero)
  let T := O₁.imp N₁
  have hb : FormulaProves ((baseRelation ⊓ N).imp T) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    let Γ := [O₁, baseRelation ⊓ N]
    have hp : FOL.Context Peano.Axiom Γ (baseRelation ⊓ N) := .hypothesis (by simp [Γ])
    have hR := FOL.Context.conjunctionLeft hp
    have hn := FOL.Context.conjunctionRight hp
    have ho : FOL.Context Peano.Axiom Γ O := by
      have hc := PeanoBetaAppendCases.old_case zero (succ (.var 0)) O
        ((.var 3 : Peano.Term).equal (add (.var 6) (.var 6)))
      exact .mp (.mp (.closed (by simpa [baseRelation, O] using hc)) hR)
        (.closed (PeanoOrderTotality.zero_less_succ (.var 0)))
    have he : FOL.Context Peano.Axiom Γ ((.var 3 : Peano.Term).equal (succ zero)) :=
      .mp (.mp (.closed (PeanoBetaUnique.beta_unique (.var 4) (.var 5) zero (.var 3) (succ zero))) ho)
        (FOL.Context.head _ _)
    exact .mp (.mp (.closed (PeanoBetaRowTransfer.beta_output_congr
      (.var 9) (.var 1) zero (.var 3) (succ zero))) he) hn
  have hf : 3 ∉ T.freeVarFinset := by decide
  have helim := PeanoBitPositionReduction.exists_elim 3 hf hb
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  let G := rowsAt appendRelation (succ (succ (.var 0))) 9
  let Γ := [O₁,G]
  have hg : FOL.Context Peano.Axiom Γ G := .hypothesis (by simp [Γ])
  have hinst : FOL.Context Peano.Axiom Γ
      ((less zero (succ (succ (.var 0)))).imp (FOL.existsAt 3 (baseRelation ⊓ N))) := by
    have hi := FOL.Derivation.logical (Axiom := Peano.Axiom)
      (FOL.LogicalAxiom.allElim
        ((less (.var 2) (succ (succ (.var 0)))).imp
          (FOL.existsAt 3 (appendRelation ⊓ beta (.var 9) (.var 1) (.var 2) (.var 3)))) 2 zero)
    rw [row_instance_syntax] at hi
    exact .mp (.closed hi) hg
  have he : FOL.Context Peano.Axiom Γ (FOL.existsAt 3 (baseRelation ⊓ N)) :=
    .mp hinst (.closed (PeanoOrderTotality.zero_less_succ (succ (.var 0))))
  exact .mp (.mp (.closed helim) he) (FOL.Context.head _ _)

end PASoundness.PeanoBetaAppendBase

#print axioms PASoundness.PeanoBetaAppendBase.initial_row_preserved
