import PASoundness.PeanoBetaCRTDependentLift

/-! Exact fixed-name CRT dependent-use wrapper. The three PA component
updates and the local witness existence remain explicit premises. -/
namespace PASoundness.PeanoBetaCRTDependentComponents
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic
open PeanoBetaCRTInvariant PeanoBetaCRTDependentLift

private theorem substAt_both (φ ψ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    FOL.substAt (φ ⊓ ψ) x t = (FOL.substAt φ x t ⊓ FOL.substAt ψ x t) := rfl

/-- Under the same selected condition and with the same output terms `b,p`,
three supplied PA component derivations construct `hUse` for the dependent
CRT witness lift. This proves no component update or witness existence. The
indicated name freshness prevents output existential binders 11,12 from
capturing the relation's parameters or appearing in the output terms. -/
theorem use_selected_components (φ S W : Peano.Formula) (b p : Peano.Term)
    (_hφ11 : 11 ∉ φ.freeVarFinset) (_hφ12 : 12 ∉ φ.freeVarFinset)
    (_hb11 : 11 ∉ b.varFinset) (_hb12 : 12 ∉ b.varFinset)
    (_hp11 : 11 ∉ p.varFinset) (_hp12 : 12 ∉ p.varFinset)
    (hRows : FormulaProves (S.imp ((currentMatrix φ).imp (W.imp
      (FOL.substAt (FOL.substAt (nextRows φ) 11 b) 12 p)))))
    (hFactors : FormulaProves (S.imp ((currentMatrix φ).imp (W.imp
      (FOL.substAt (FOL.substAt nextFactors 11 b) 12 p)))))
    (hFuture : FormulaProves (S.imp ((currentMatrix φ).imp (W.imp
      (FOL.substAt (FOL.substAt nextFuture 11 b) 12 p))))) :
    FormulaProves (S.imp ((currentMatrix φ).imp (W.imp (nextInvariant φ)))) := by
  let C := currentMatrix φ
  let N := nextMatrix φ
  let K := ((S ⊓ C) ⊓ W)
  let Γ := [K]
  have hUpdate : FormulaProves (K.imp (FOL.substAt (FOL.substAt N 11 b) 12 p)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    have hk : FOL.Context Peano.Axiom Γ K := FOL.Context.head [] K
    have hs : FOL.Context Peano.Axiom Γ S := FOL.Context.conjunctionLeft (FOL.Context.conjunctionLeft hk)
    have hc : FOL.Context Peano.Axiom Γ C := FOL.Context.conjunctionRight (FOL.Context.conjunctionLeft hk)
    have hw : FOL.Context Peano.Axiom Γ W := FOL.Context.conjunctionRight hk
    have hr := FOL.Context.mp (FOL.Context.mp (FOL.Context.mp (.closed hRows) hs) hc) hw
    have hd := FOL.Context.mp (FOL.Context.mp (FOL.Context.mp (.closed hFactors) hs) hc) hw
    have hf := FOL.Context.mp (FOL.Context.mp (FOL.Context.mp (.closed hFuture) hs) hc) hw
    have hconj := FOL.Context.conjunctionIntro (FOL.Context.conjunctionIntro hr hd) hf
    simpa only [N, nextMatrix, substAt_both] using hconj
  have hi : FormulaProves (K.imp (nextInvariant φ)) := by
    simpa only [nextInvariant] using introduce_pair K N 12 11 p b hUpdate
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  let Δ := [W,C,S]
  have hs : FOL.Context Peano.Axiom Δ S :=
    FOL.Context.under (FOL.Context.under (FOL.Context.head [] S) C) W
  have hc : FOL.Context Peano.Axiom Δ C := FOL.Context.under (FOL.Context.head [S] C) W
  have hw : FOL.Context Peano.Axiom Δ W := FOL.Context.head _ _
  exact .mp (.closed hi) (FOL.Context.conjunctionIntro (FOL.Context.conjunctionIntro hs hc) hw)

/-- Compose the exact shared-witness component rule with the reviewed dependent
triple lift. Local witnesses may depend on the current code/product; freshness
and witness selection remain explicit hypotheses. -/
theorem dependent_components_successor (φ S W : Peano.Formula) (u v r : Nat) (b p : Peano.Term)
    (hφ9 : 9 ∉ φ.freeVarFinset) (hφ10 : 10 ∉ φ.freeVarFinset)
    (hφ11 : 11 ∉ φ.freeVarFinset) (hφ12 : 12 ∉ φ.freeVarFinset)
    (hb11 : 11 ∉ b.varFinset) (hb12 : 12 ∉ b.varFinset)
    (hp11 : 11 ∉ p.varFinset) (hp12 : 12 ∉ p.varFinset)
    (ha9 : 9 ∉ S.freeVarFinset) (ha10 : 10 ∉ S.freeVarFinset)
    (huS : u ∉ S.freeVarFinset) (huC : u ∉ (currentMatrix φ).freeVarFinset)
    (huT : u ∉ (nextInvariant φ).freeVarFinset)
    (hvS : v ∉ S.freeVarFinset) (hvC : v ∉ (currentMatrix φ).freeVarFinset)
    (hvT : v ∉ (nextInvariant φ).freeVarFinset)
    (hrS : r ∉ S.freeVarFinset) (hrC : r ∉ (currentMatrix φ).freeVarFinset)
    (hrT : r ∉ (nextInvariant φ).freeVarFinset)
    (hExists : FormulaProves (S.imp ((currentMatrix φ).imp
      (FOL.existsAt u (FOL.existsAt v (FOL.existsAt r W))))))
    (hRows : FormulaProves (S.imp ((currentMatrix φ).imp (W.imp
      (FOL.substAt (FOL.substAt (nextRows φ) 11 b) 12 p)))))
    (hFactors : FormulaProves (S.imp ((currentMatrix φ).imp (W.imp
      (FOL.substAt (FOL.substAt nextFactors 11 b) 12 p)))))
    (hFuture : FormulaProves (S.imp ((currentMatrix φ).imp (W.imp
      (FOL.substAt (FOL.substAt nextFuture 11 b) 12 p))))) :
    FormulaProves (S.imp ((currentInvariant φ).imp (nextInvariant φ))) := by
  exact dependent_crt_successor φ S W u v r hφ9 hφ10 ha9 ha10
    huS huC huT hvS hvC hvT hrS hrC hrT hExists
    (use_selected_components φ S W b p hφ11 hφ12 hb11 hb12 hp11 hp12 hRows hFactors hFuture)

end PASoundness.PeanoBetaCRTDependentComponents
