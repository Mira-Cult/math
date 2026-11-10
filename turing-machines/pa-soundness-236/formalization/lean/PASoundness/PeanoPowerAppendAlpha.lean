import PASoundness.PeanoBetaCRTAlpha
import PASoundness.PeanoPowerAppendIntro

/-! Capture-safe renaming of the two witnesses of a supplied beta trace.
The input trace is a premise; this file does not construct one. -/
namespace PASoundness.PeanoPowerAppendAlpha
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic PeanoBetaCRTAlpha

def transitionBody (r s : Peano.Term) : Peano.Formula :=
  beta (.var 9) (.var 1) (.var 2) r ⊓
    (beta (.var 9) (.var 1) (succ (.var 2)) s ⊓ (s.equal (add r r)))

def highRows : Peano.Formula := FOL.existsAt 20 (FOL.existsAt 21
  (transitionBody (.var 20) (.var 21)))

def lowRows : Peano.Formula := FOL.existsAt 3 (FOL.existsAt 4
  (transitionBody (.var 3) (.var 4)))

def highFamily : Peano.Formula := FOL.allAt 2
  ((less (.var 2) (succ (.var 0))).imp highRows)

def lowFamily : Peano.Formula := FOL.allAt 2
  ((less (.var 2) (succ (.var 0))).imp lowRows)

private theorem subst_not (φ : Peano.Formula) (σ : Nat → Peano.Term) :
    φ.not.subst σ = (φ.subst σ).not := by
  simp [FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.mapTermRel]
  rfl

private theorem subst_and (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ ⊓ ψ).subst σ = (φ.subst σ) ⊓ (ψ.subst σ) := by
  change (φ.imp ψ.not).not.subst σ = ((φ.subst σ).imp (ψ.subst σ).not).not
  rw [subst_not, show (φ.imp ψ.not).subst σ = (φ.subst σ).imp (ψ.not.subst σ) from rfl, subst_not]

theorem subst_first : FOL.substAt (transitionBody (.var 20) (.var 21)) 20 (.var 3) =
    transitionBody (.var 3) (.var 21) := by
  simp [FOL.substAt, transitionBody, subst_and, beta_subst, FOL.equality_subst, add_subst,
    succ_subst, FirstOrder.Language.Term.subst]

theorem subst_second : FOL.substAt (transitionBody (.var 3) (.var 21)) 21 (.var 4) =
    transitionBody (.var 3) (.var 4) := by
  simp [FOL.substAt, transitionBody, subst_and, beta_subst, FOL.equality_subst, add_subst,
    succ_subst, FirstOrder.Language.Term.subst]

private theorem outer_alpha : FormulaProves (highRows.imp
    (FOL.existsAt 3 (FOL.existsAt 21 (transitionBody (.var 3) (.var 21))))) := by
  have hf : 3 ∉ (FOL.existsAt 21 (transitionBody (.var 20) (.var 21))).freeVarFinset := by decide
  have h := exists_alpha_forward (FOL.existsAt 21 (transitionBody (.var 20) (.var 21)))
    20 3 (by decide) hf
  rw [subst_var_existsAt _ 20 3 21 (by decide) (by decide), subst_first] at h
  exact h

/-- The witnesses are renamed separately, with their freshness checked. -/
theorem rows_alpha : FormulaProves (highRows.imp lowRows) := by
  let B := transitionBody (.var 3) (.var 21)
  let C := transitionBody (.var 3) (.var 4)
  have hf : 4 ∉ B.freeVarFinset := by decide
  have hi : FormulaProves ((FOL.existsAt 21 B).imp (FOL.existsAt 4 C)) := by
    simpa only [B, C, subst_second] using (exists_alpha_forward B 21 4 (by decide) hf)
  have hp : FormulaProves ((FOL.existsAt 4 C).imp lowRows) := by
    simpa only [lowRows, C, SyntaxTransport.substAt_self] using
      (FOL.Derivation.existsIntro (A := Peano.Axiom) (FOL.existsAt 4 C) 3 (.var 3))
  have hlocal := FOL.Derivation.compose hi hp
  have hfree : 3 ∉ lowRows.freeVarFinset := by decide
  have hlift := PeanoBitPositionReduction.exists_elim 3 hfree hlocal
  exact FOL.Derivation.compose outer_alpha hlift

/-- Lift the local renaming across the guarded, universally quantified family. -/
theorem family_alpha : FormulaProves (highFamily.imp lowFamily) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  change FOL.Context Peano.Axiom [highFamily] (FOL.allAt 2
    ((less (.var 2) (succ (.var 0))).imp lowRows))
  apply FOL.Context.generalize 2
  · intro ψ hψ
    have he : ψ = highFamily := by simpa only [List.mem_singleton] using hψ
    subst ψ
    simp [highFamily, SyntaxTransport.allAt_freeVars]
  · apply FOL.Context.deduction
    let L := less (.var 2) (succ (.var 0))
    have hf : FOL.Context Peano.Axiom [L, highFamily] (L.imp highRows) :=
      FOL.Context.allSelf (FOL.Context.under (FOL.Context.head [] highFamily) L)
    have hr : FOL.Context Peano.Axiom [L, highFamily] highRows :=
      .mp hf (FOL.Context.head _ _)
    exact .mp (.closed rows_alpha) hr

/-- Once the full renamed family and two endpoint rows are supplied, PA
packages them into the literal successor-power formula. -/
theorem family_to_power : FormulaProves
    (highFamily.imp ((beta (.var 9) (.var 1) zero (succ zero)).imp
      ((beta (.var 9) (.var 1) (succ (.var 0)) (add (.var 6) (.var 6))).imp
        (pow2 (succ (.var 0)) (add (.var 6) (.var 6)))))) := by
  let Z := beta (.var 9) (.var 1) zero (succ zero)
  let E := beta (.var 9) (.var 1) (succ (.var 0)) (add (.var 6) (.var 6))
  let Γ := [E,Z,highFamily]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hf : FOL.Context Peano.Axiom Γ highFamily := .hypothesis (by simp [Γ])
  have hz : FOL.Context Peano.Axiom Γ Z := .hypothesis (by simp [Γ])
  have he : FOL.Context Peano.Axiom Γ E := FOL.Context.head _ _
  have hl : FOL.Context Peano.Axiom Γ lowFamily := .mp (.closed family_alpha) hf
  have hm : FOL.Context Peano.Axiom Γ PeanoPowerAppendIntro.traceMatrix := by
    exact FOL.Context.conjunctionIntro hz (FOL.Context.conjunctionIntro he hl)
  exact .mp (.closed PeanoPowerAppendIntro.trace_to_power) hm

end PASoundness.PeanoPowerAppendAlpha

#print axioms PASoundness.PeanoPowerAppendAlpha.rows_alpha
#print axioms PASoundness.PeanoPowerAppendAlpha.family_alpha
#print axioms PASoundness.PeanoPowerAppendAlpha.family_to_power
