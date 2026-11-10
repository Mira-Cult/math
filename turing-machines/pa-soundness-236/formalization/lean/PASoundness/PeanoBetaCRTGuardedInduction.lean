import PASoundness.PeanoBetaCRTInductionBridge
import PASoundness.PeanoOrderSuccessor
import PASoundness.PeanoOrderTransitive
import PASoundness.PeanoPowerTransition

/-! Guarded PA induction scaffold for the beta CRT invariant. The actual PA
successor update is an explicit proof premise; this module does not establish
that premise, bounded CRT, or beta-trace existence. -/
namespace PASoundness.PeanoBetaCRTGuardedInduction
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoBetaCRTInvariant

/-- Guard the invariant by k < S N, with k=name 7 and N=name 8. -/
def guarded (φ : Peano.Formula) : Peano.Formula :=
  (less (.var 7) (succ (.var 8))).imp (currentInvariant φ)

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := rfl

/-- Capture-safe substitution of zero into the guarded invariant. -/
theorem guarded_zero_syntax (φ : Peano.Formula) :
    FOL.substAt (guarded φ) 7 zero =
      ((less zero (succ (.var 8))).imp (FOL.substAt (currentInvariant φ) 7 zero)) := by
  simp only [FOL.substAt, guarded, subst_imp, less_subst, succ_subst,
    FirstOrder.Language.Term.subst, ↓reduceIte,
    show (8 : Nat) ≠ 7 by decide]

/-- Capture-safe substitution of S k into the guarded invariant. -/
theorem guarded_succ_syntax (φ : Peano.Formula) :
    FOL.substAt (guarded φ) 7 (succ (.var 7)) =
      ((less (succ (.var 7)) (succ (.var 8))).imp
        (FOL.substAt (currentInvariant φ) 7 (succ (.var 7)))) := by
  simp only [FOL.substAt, guarded, subst_imp, less_subst, succ_subst,
    FirstOrder.Language.Term.subst, ↓reduceIte, show (8 : Nat) ≠ 7 by decide]

/-- PA derives the guarded base from the already established literal base. -/
theorem guarded_base (φ : Peano.Formula)
    (hφ7 : 7 ∉ φ.freeVarFinset) (hφ9 : 9 ∉ φ.freeVarFinset)
    (hφ10 : 10 ∉ φ.freeVarFinset) :
    FormulaProves (FOL.substAt (guarded φ) 7 zero) := by
  rw [guarded_zero_syntax]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  exact .closed (PeanoBetaCRTInductionBridge.literal_base φ hφ7 hφ9 hφ10)

/-- Under a fixed global condition G, a supplied PA derivation of the update
for k<N produces the literal guarded induction step. G is not asserted. -/
theorem guarded_step (φ G : Peano.Formula)
    (hStep : FormulaProves (G.imp ((less (.var 7) (.var 8)).imp
      ((currentInvariant φ).imp (FOL.substAt (currentInvariant φ) 7 (succ (.var 7))))))) :
    FormulaProves (G.imp ((guarded φ).imp (FOL.substAt (guarded φ) 7 (succ (.var 7))))) := by
  let H := guarded φ
  let L := less (succ (.var 7)) (succ (.var 8))
  let Γ := [L,H,G]
  rw [guarded_succ_syntax]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hg : FOL.Context Peano.Axiom Γ G := .hypothesis (by simp [Γ])
  have hh : FOL.Context Peano.Axiom Γ H := .hypothesis (by simp [Γ])
  have hl : FOL.Context Peano.Axiom Γ L := FOL.Context.head _ _
  have hkn : FOL.Context Peano.Axiom Γ (less (.var 7) (.var 8)) :=
    .mp (.closed (PeanoOrderSuccessor.less_succ_iff (.var 7) (.var 8)).2) hl
  have hksn : FOL.Context Peano.Axiom Γ (less (.var 7) (succ (.var 8))) :=
    .mp (.mp (.closed (PeanoOrderTransitive.less_transitive_all (.var 7) (.var 8) (succ (.var 8)))) hkn)
      (.closed (PeanoPowerTransition.self_less_succ (.var 8)))
  have hi : FOL.Context Peano.Axiom Γ (currentInvariant φ) := .mp hh hksn
  exact .mp (.mp (.mp (.closed hStep) hg) hkn) hi

/-- If G is independent of k, PA induction derives the invariant at the
capture-safe instance k=N. This is conditional on the displayed derivation of
the k<N update, and does not establish it or bounded CRT. -/
theorem guarded_endpoint (φ G : Peano.Formula)
    (hφ7 : 7 ∉ φ.freeVarFinset) (hφ9 : 9 ∉ φ.freeVarFinset)
    (hφ10 : 10 ∉ φ.freeVarFinset) (hG7 : 7 ∉ G.freeVarFinset)
    (hStep : FormulaProves (G.imp ((less (.var 7) (.var 8)).imp
      ((currentInvariant φ).imp (FOL.substAt (currentInvariant φ) 7 (succ (.var 7))))))) :
    FormulaProves (G.imp (FOL.substAt (currentInvariant φ) 7 (.var 8))) := by
  let H := guarded φ
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have hg : FOL.Context Peano.Axiom [G] G := FOL.Context.head [] G
  have hstep : FOL.Context Peano.Axiom [G]
      (FOL.allAt 7 (H.imp (FOL.substAt H 7 (succ (.var 7))))) := by
    apply FOL.Context.generalize 7
    · intro ψ hψ
      have he : ψ = G := by simpa using hψ
      subst ψ
      exact hG7
    · exact .mp (.closed (guarded_step φ G hStep)) hg
  have hind : FOL.Context Peano.Axiom [G] (FOL.allAt 7 H) :=
    .mp (.mp (.closed (.axiom (.induction H 7)))
      (.closed (guarded_base φ hφ7 hφ9 hφ10))) hstep
  have hs := FOL.Context.allElim hind (.var 8)
  have hinst : FOL.Context Peano.Axiom [G]
      ((less (.var 8) (succ (.var 8))).imp (FOL.substAt (currentInvariant φ) 7 (.var 8))) := by
    simpa only [H, FOL.substAt, guarded, subst_imp, less_subst, succ_subst,
      FirstOrder.Language.Term.subst, ↓reduceIte, show (8 : Nat) ≠ 7 by decide] using hs
  exact .mp hinst (.closed (PeanoPowerTransition.self_less_succ (.var 8)))

end PASoundness.PeanoBetaCRTGuardedInduction
