import PASoundness.PeanoBetaCRTInvariant

/-! Logical packaging for dependent CRT update witnesses. Local witnesses may
refer to the current code/product; no witness existence or CRT result is proved. -/
namespace PASoundness.PeanoBetaCRTDependentLift
open FirstOrder FirstOrder.Language
open PASoundness.Peano

/-- Eliminate an existentially supplied triple of local witnesses while the
current state remains in scope. No assertion about witness existence or
transition components is made by this logical rule. -/
theorem use_local_triple (S C W T : Peano.Formula) (u v r : Nat)
    (huS : u ∉ S.freeVarFinset) (huC : u ∉ C.freeVarFinset) (huT : u ∉ T.freeVarFinset)
    (hvS : v ∉ S.freeVarFinset) (hvC : v ∉ C.freeVarFinset) (hvT : v ∉ T.freeVarFinset)
    (hrS : r ∉ S.freeVarFinset) (hrC : r ∉ C.freeVarFinset) (hrT : r ∉ T.freeVarFinset)
    (hExists : FormulaProves (S.imp (C.imp (FOL.existsAt u (FOL.existsAt v (FOL.existsAt r W))))))
    (hUse : FormulaProves (S.imp (C.imp (W.imp T)))) : FormulaProves (S.imp (C.imp T)) := by
  have hswap : FormulaProves (W.imp (S.imp (C.imp T))) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    let Γ := [C,S,W]
    have hS : FOL.Context Peano.Axiom Γ S :=
      FOL.Context.under (FOL.Context.head [W] S) C
    have hC : FOL.Context Peano.Axiom Γ C := FOL.Context.head _ _
    have hW : FOL.Context Peano.Axiom Γ W :=
      FOL.Context.under (FOL.Context.under (FOL.Context.head [] W) S) C
    exact .mp (.mp (.mp (.closed hUse) hS) hC) hW
  have hu : u ∉ (S.imp (C.imp T)).freeVarFinset := by
    simpa [FirstOrder.Language.BoundedFormula.freeVarFinset] using And.intro huS (And.intro huC huT)
  have hv : v ∉ (S.imp (C.imp T)).freeVarFinset := by
    simpa [FirstOrder.Language.BoundedFormula.freeVarFinset] using And.intro hvS (And.intro hvC hvT)
  have hr : r ∉ (S.imp (C.imp T)).freeVarFinset := by
    simpa [FirstOrder.Language.BoundedFormula.freeVarFinset] using And.intro hrS (And.intro hrC hrT)
  have hR := PeanoBitPositionReduction.exists_elim r hr hswap
  have hV := PeanoBitPositionReduction.exists_elim v hv hR
  have hU := PeanoBitPositionReduction.exists_elim u hu hV
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hS : FOL.Context Peano.Axiom [C,S] S := FOL.Context.under (FOL.Context.head [] S) C
  have hC : FOL.Context Peano.Axiom [C,S] C := FOL.Context.head _ _
  exact .mp (.mp (.mp (.closed hU) (.mp (.mp (.closed hExists) hS) hC)) hS) hC



/-- Eliminate the old state pair after a PA derivation has established the
entire target while the old witnesses are still exposed. Local side formulas
inside that derivation may depend on both old witnesses. -/
theorem exists_state_update_under (S C T : Peano.Formula) (oldP oldB : Nat)
    (haP : oldP ∉ S.freeVarFinset) (haB : oldB ∉ S.freeVarFinset)
    (htP : oldP ∉ T.freeVarFinset) (htB : oldB ∉ T.freeVarFinset)
    (hUpdate : FormulaProves (S.imp (C.imp T))) :
    FormulaProves (S.imp ((FOL.existsAt oldP (FOL.existsAt oldB C)).imp T)) := by
  have hswap : FormulaProves (C.imp (S.imp T)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    have hc : FOL.Context Peano.Axiom [S,C] C :=
      FOL.Context.under (FOL.Context.head [] C) S
    have hs : FOL.Context Peano.Axiom [S,C] S := FOL.Context.head _ _
    exact .mp (.mp (.closed hUpdate) hs) hc
  have hfB : oldB ∉ (S.imp T).freeVarFinset := by
    simpa [FirstOrder.Language.BoundedFormula.freeVarFinset] using And.intro haB htB
  have hfP : oldP ∉ (S.imp T).freeVarFinset := by
    simpa [FirstOrder.Language.BoundedFormula.freeVarFinset] using And.intro haP htP
  have heB := PeanoBitPositionReduction.exists_elim oldB hfB hswap
  have heP := PeanoBitPositionReduction.exists_elim oldP hfP heB
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  let Q := FOL.existsAt oldP (FOL.existsAt oldB C)
  have hs : FOL.Context Peano.Axiom [Q,S] S :=
    FOL.Context.under (FOL.Context.head [] S) Q
  have hq : FOL.Context Peano.Axiom [Q,S] Q := FOL.Context.head _ _
  exact .mp (.mp (.closed heP) hq) hs

/-- First choose a local witness triple under the exposed current state, use
it to establish the target, then eliminate the old state pair. The selected
formula W may freely mention the old witnesses; only the external side
condition S and final target T must be fresh for them. -/
theorem dependent_triple_state_update (S C W T : Peano.Formula)
    (oldP oldB u v r : Nat)
    (haP : oldP ∉ S.freeVarFinset) (haB : oldB ∉ S.freeVarFinset)
    (htP : oldP ∉ T.freeVarFinset) (htB : oldB ∉ T.freeVarFinset)
    (huS : u ∉ S.freeVarFinset) (huC : u ∉ C.freeVarFinset) (huT : u ∉ T.freeVarFinset)
    (hvS : v ∉ S.freeVarFinset) (hvC : v ∉ C.freeVarFinset) (hvT : v ∉ T.freeVarFinset)
    (hrS : r ∉ S.freeVarFinset) (hrC : r ∉ C.freeVarFinset) (hrT : r ∉ T.freeVarFinset)
    (hExists : FormulaProves (S.imp (C.imp (FOL.existsAt u (FOL.existsAt v (FOL.existsAt r W))))))
    (hUse : FormulaProves (S.imp (C.imp (W.imp T)))) :
    FormulaProves (S.imp ((FOL.existsAt oldP (FOL.existsAt oldB C)).imp T)) :=
  exists_state_update_under S C T oldP oldB haP haB htP htB
    (use_local_triple S C W T u v r huS huC huT hvS hvC hvT hrS hrC hrT hExists hUse)


private theorem fv_inf (φ ψ : Peano.Formula) :
    (φ ⊓ ψ).freeVarFinset = φ.freeVarFinset ∪ ψ.freeVarFinset := by
  change ((φ.imp ψ.not).not).freeVarFinset = _
  simp [FirstOrder.Language.BoundedFormula.freeVarFinset]

private theorem fv_exists (φ : Peano.Formula) (x : Nat) :
    (FOL.existsAt x φ).freeVarFinset = φ.freeVarFinset.erase x := by
  simp [FOL.existsAt, SyntaxTransport.allAt_freeVars,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.freeVarFinset]

open PeanoArithmetic CompactArithmetic PeanoDivisibility PeanoBetaCRTInvariant

/-- The target of the fixed CRT successor update is fresh for old state names
when the row relation is fresh for those names. -/
theorem next_state_fresh (φ : Peano.Formula)
    (hφ9 : 9 ∉ φ.freeVarFinset) (hφ10 : 10 ∉ φ.freeVarFinset) :
    9 ∉ (nextInvariant φ).freeVarFinset ∧ 10 ∉ (nextInvariant φ).freeVarFinset := by
  have hf9 : 9 ∉ (nextInvariant φ).freeVarFinset := by
    have ha : 9 ∉ (less (.var 2) (succ (.var 7))).freeVarFinset := by decide
    have hb : 9 ∉ (beta (.var 11) (.var 1) (.var 2) (.var 3)).freeVarFinset := by decide
    have hc : 9 ∉ (divides (modulus (.var 1) (.var 2)) (.var 12)).freeVarFinset := by decide
    have hd : 9 ∉ (less (.var 2) (.var 8)).freeVarFinset := by decide
    have he : 9 ∉ (((mul (.var 12) (.var 3)).equal
      (add (succ zero) (mul (.var 4) (modulus (.var 1) (.var 2)))) : Peano.Formula)).freeVarFinset := by decide
    simp [nextInvariant, nextMatrix, nextRows, nextFactors, nextFuture, rowsAt,
      factorsAt, futureAt, fv_exists, fv_inf, SyntaxTransport.allAt_freeVars,
      FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.freeVarFinset,
      hφ9, ha, hb, hc, hd, he]
  have hf10 : 10 ∉ (nextInvariant φ).freeVarFinset := by
    have ha : 10 ∉ (less (.var 2) (succ (.var 7))).freeVarFinset := by decide
    have hb : 10 ∉ (beta (.var 11) (.var 1) (.var 2) (.var 3)).freeVarFinset := by decide
    have hc : 10 ∉ (divides (modulus (.var 1) (.var 2)) (.var 12)).freeVarFinset := by decide
    have hd : 10 ∉ (less (.var 2) (.var 8)).freeVarFinset := by decide
    have he : 10 ∉ (((mul (.var 12) (.var 3)).equal
      (add (succ zero) (mul (.var 4) (modulus (.var 1) (.var 2)))) : Peano.Formula)).freeVarFinset := by decide
    simp [nextInvariant, nextMatrix, nextRows, nextFactors, nextFuture, rowsAt,
      factorsAt, futureAt, fv_exists, fv_inf, SyntaxTransport.allAt_freeVars,
      FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.freeVarFinset,
      hφ10, ha, hb, hc, hd, he]
  exact ⟨hf9, hf10⟩

/-- CRT-state specialization of dependent triple selection. The selected
condition W may mention the exposed old code and product; its witness
existence and its use remain explicit PA-derivation premises. -/
theorem dependent_crt_successor (φ S W : Peano.Formula) (u v r : Nat)
    (hφ9 : 9 ∉ φ.freeVarFinset) (hφ10 : 10 ∉ φ.freeVarFinset)
    (ha9 : 9 ∉ S.freeVarFinset) (ha10 : 10 ∉ S.freeVarFinset)
    (huS : u ∉ S.freeVarFinset) (huC : u ∉ (currentMatrix φ).freeVarFinset)
    (huT : u ∉ (nextInvariant φ).freeVarFinset)
    (hvS : v ∉ S.freeVarFinset) (hvC : v ∉ (currentMatrix φ).freeVarFinset)
    (hvT : v ∉ (nextInvariant φ).freeVarFinset)
    (hrS : r ∉ S.freeVarFinset) (hrC : r ∉ (currentMatrix φ).freeVarFinset)
    (hrT : r ∉ (nextInvariant φ).freeVarFinset)
    (hExists : FormulaProves (S.imp ((currentMatrix φ).imp
      (FOL.existsAt u (FOL.existsAt v (FOL.existsAt r W))))))
    (hUse : FormulaProves (S.imp ((currentMatrix φ).imp (W.imp (nextInvariant φ))))) :
    FormulaProves (S.imp ((currentInvariant φ).imp (nextInvariant φ))) := by
  have hf := next_state_fresh φ hφ9 hφ10
  simpa only [currentInvariant, currentMatrix, invariantAt, invariantWith] using
    dependent_triple_state_update S (currentMatrix φ) W (nextInvariant φ)
      10 9 u v r ha10 ha9 hf.2 hf.1 huS huC huT hvS hvC hvT hrS hrC hrT hExists hUse

end PASoundness.PeanoBetaCRTDependentLift
