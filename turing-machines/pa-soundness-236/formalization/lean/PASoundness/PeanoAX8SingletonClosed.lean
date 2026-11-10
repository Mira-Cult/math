import PASoundness.PeanoAX8SingletonCombine

/-! Conditional alias-case singleton extraction from the universal bounded
invariant. This does not establish the invariant or literal AX8 alignment. -/
namespace PASoundness.PeanoAX8SingletonClosed
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoFiniteComprehensionBase PeanoAX8SingletonCombine

/-- PA chooses a length strictly above the outer index. -/
theorem outer_bound_exists : FormulaProves
    (FOL.existsAt 0 (less (.var 5) (.var 0))) := by
  have h := FOL.Derivation.existsIntro (A := Peano.Axiom)
    (less (.var 5) (.var 0)) 0 (succ (.var 5))
  have hs : FOL.substAt (less (.var 5) (.var 0)) 0 (succ (.var 5)) =
      less (.var 5) (succ (.var 5)) := by
    simp [FOL.substAt, less_subst, FirstOrder.Language.Term.subst]
  rw [hs] at h
  exact .mp h (PeanoPowerTransition.self_less_succ (.var 5))

/-- Given the universal bounded singleton invariant, PA chooses a length
above the outer index and retains one code satisfying both reduced alias
obligations. ψ must be fresh for the length and existential witness names. -/
theorem singleton_of_universal (ψ : Peano.Formula)
    (hψ0 : 0 ∉ ψ.freeVarFinset) (hψ2 : 2 ∉ ψ.freeVarFinset)
    (hψ3 : 3 ∉ ψ.freeVarFinset) :
    FormulaProves ((FOL.allAt 0
      (invariant (PeanoAX8SingletonSelector.selector ψ) (.var 0))).imp
      (FOL.existsAt 3 (aliasConsequences ψ))) := by
  let I := invariant (PeanoAX8SingletonSelector.selector ψ) (.var 0)
  let U := FOL.allAt 0 I
  let H := less (.var 5) (.var 0)
  let T := FOL.existsAt 3 (aliasConsequences ψ)
  have hbody : FormulaProves (H.imp (U.imp T)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    let Γ := [U, H]
    have hu : FOL.Context Peano.Axiom Γ U := .head _ _
    have hh : FOL.Context Peano.Axiom Γ H := .hypothesis (by simp [Γ])
    have hi : FOL.Context Peano.Axiom Γ I := FOL.Context.allSelf hu
    exact .mp (.mp (.closed (singleton_solution ψ hψ2 hψ3)) hi) hh
  have hsub : 0 ∉ (FOL.substAt ψ 1 (.var 5)).freeVarFinset := by
    intro h
    unfold FOL.substAt at h
    rw [SyntaxTransport.formula_subst_freeVars] at h
    obtain ⟨x, hx, hterm⟩ := h
    by_cases h1 : x = 1
    · subst x
      simp [FirstOrder.Language.Term.varFinset] at hterm
    · have h0x : (0 : Nat) = x := by
        simpa [h1, FirstOrder.Language.Term.varFinset] using hterm
      have hx0 : x = 0 := h0x.symm
      subst x
      exact hψ0 hx
  have hT : 0 ∉ T.freeVarFinset := by
    have hb1 : 0 ∉ (bitFormula (.var 3) (.var 1)).freeVarFinset := by decide
    have hb5 : 0 ∉ (bitFormula (.var 3) (.var 5)).freeVarFinset := by decide
    change 0 ∉ (FOL.existsAt 3
      (((FOL.allAt 1 ((bitFormula (.var 3) (.var 1)).imp ψ)).imp
        ((FOL.substAt ψ 1 (.var 5)).imp (bitFormula (.var 3) (.var 5))).not).not)).freeVarFinset
    simp [FOL.existsAt, SyntaxTransport.allAt_freeVars,
      FirstOrder.Language.BoundedFormula.freeVarFinset, hb1, hψ0, hsub, hb5]
  have hU : 0 ∉ U.freeVarFinset := by
    simp [U, SyntaxTransport.allAt_freeVars]
  have hf : 0 ∉ (U.imp T).freeVarFinset := by
    simp [FirstOrder.Language.BoundedFormula.freeVarFinset, hU, hT]
  have he := PeanoBitPositionReduction.exists_elim 0 hf hbody
  exact .mp he outer_bound_exists

end PASoundness.PeanoAX8SingletonClosed

#print axioms PASoundness.PeanoAX8SingletonClosed.outer_bound_exists
#print axioms PASoundness.PeanoAX8SingletonClosed.singleton_of_universal
