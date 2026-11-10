import PASoundness.PeanoBetaCRTRecordMerge
import PASoundness.PeanoBetaCRTAlpha

/-! A PA family merge with an explicitly substituted boundary formula.
It does not assert either premise or a trace-existence theorem. -/
namespace PASoundness.PeanoBetaAppendFamilyMerge
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

private theorem or_elim {L : Language} {A : FOL.Formula L → Prop}
    {Γ : List (FOL.Formula L)} {φ ψ χ : FOL.Formula L}
    (h : FOL.Context A Γ (φ ⊔ ψ)) (hφ : FOL.Context A Γ (φ.imp χ))
    (hψ : FOL.Context A Γ (ψ.imp χ)) : FOL.Context A Γ χ := by
  apply FOL.Context.dne
  apply FOL.Context.deduction
  have hnφ : FOL.Context A (χ.not :: Γ) φ.not :=
    .mp (FOL.Context.under (FOL.Context.contrapose hφ) χ.not) (FOL.Context.head Γ χ.not)
  have hψ' : FOL.Context A (χ.not :: Γ) ψ :=
    .mp (FOL.Context.under h χ.not) hnφ
  exact .mp (FOL.Context.head Γ χ.not) (.mp (FOL.Context.under hψ χ.not) hψ')

/-- With `i=2` and `n=0`, the old family together with the literal
capture-safe boundary instance entails the family for `i<S n`. -/
theorem merge_family (φ : Peano.Formula) : FormulaProves
    ((FOL.allAt 2 ((less (.var 2) (.var 0)).imp φ)).imp
      ((FOL.substAt φ 2 (.var 0)).imp
        (FOL.allAt 2 ((less (.var 2) (succ (.var 0))).imp φ)))) := by
  let E := (.var 2 : Peano.Term).equal (.var 0)
  let L := less (.var 2) (.var 0)
  let L' := less (.var 2) (succ (.var 0))
  let B := FOL.substAt φ 2 (.var 0)
  let F := FOL.allAt 2 (L.imp φ)
  let Γ := [L', B, F]
  have hfresh : 2 ∉ B.freeVarFinset :=
    PeanoBetaCRTAlpha.subst_rename_fresh φ 2 0 (by decide)
  have ht : FormulaProves (E.imp (B.imp φ)) := by
    have he : FormulaProves (((.var 0 : Peano.Term).equal (.var 2)).imp
        ((FOL.substAt φ 2 (.var 0)).imp (FOL.substAt φ 2 (.var 2)))) :=
      .logical (.eqSubst φ 2 (.var 0) (.var 2))
    have hs : FormulaProves (E.imp ((.var 0 : Peano.Term).equal (.var 2))) :=
      FOL.equality_symmetry _ _
    have he' : FormulaProves (((.var 0 : Peano.Term).equal (.var 2)).imp (B.imp φ)) := by
      simpa only [B, SyntaxTransport.substAt_self] using he
    exact FOL.Derivation.compose hs he'
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.generalize 2
  · intro ψ hψ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hψ
    rcases hψ with rfl | rfl
    · exact hfresh
    · simp
  apply FOL.Context.deduction
  have hsmall : FOL.Context Peano.Axiom Γ L' := FOL.Context.head _ _
  have hsel : FOL.Context Peano.Axiom Γ B := .hypothesis (by simp [Γ])
  have hold : FOL.Context Peano.Axiom Γ F := .hypothesis (by simp [Γ])
  have hcases : FOL.Context Peano.Axiom Γ (E ⊔ L) :=
    .mp (.closed (PeanoCommonMultiple.BoundSplit.less_successor_cases (.var 2) (.var 0))) hsmall
  have he : FOL.Context Peano.Axiom Γ (E.imp φ) := by
    apply FOL.Context.deduction
    exact .mp (.mp (.closed ht) (FOL.Context.head _ _)) (FOL.Context.under hsel E)
  have hl : FOL.Context Peano.Axiom Γ (L.imp φ) := FOL.Context.allSelf hold
  exact or_elim hcases he hl

end PASoundness.PeanoBetaAppendFamilyMerge

#print axioms PASoundness.PeanoBetaAppendFamilyMerge.merge_family
