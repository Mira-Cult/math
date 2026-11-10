import PASoundness.PeanoBetaCRTInvariant

/-! The current-invariant future family supplies inverse witnesses at k<N, and
these combine with a separately supplied bounded residue witness. This is a
selection lemma only; bounded-relation totality and the CRT step remain open. -/


/-! Select the current inverse from the guarded future family. -/
namespace PASoundness.PeanoBetaCRTSelect.Inverse
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoBetaCRTInvariant

def currentInverseBody (u v : Peano.Term) : Peano.Formula :=
  (mul (.var 10) u).equal (add (succ zero) (mul v (modulus (.var 1) (.var 7))))

def currentInverse : Peano.Formula := FOL.existsAt 14 (FOL.existsAt 15
  (currentInverseBody (.var 14) (.var 15)))

def futureBody : Peano.Formula :=
  (((less (.var 2) (.var 7)).not) ⊓ less (.var 2) (.var 8)).imp
    (FOL.existsAt 3 (FOL.existsAt 4
      ((mul (.var 10) (.var 3)).equal
        (add (succ zero) (mul (.var 4) (modulus (.var 1) (.var 2)))))))

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := rfl
private theorem subst_not (φ : Peano.Formula) (σ : Nat → Peano.Term) :
    φ.not.subst σ = (φ.subst σ).not := rfl
private theorem subst_and (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ ⊓ ψ).subst σ = ((φ.subst σ) ⊓ (ψ.subst σ)) := by
  change (φ.imp ψ.not).not.subst σ = ((φ.subst σ).imp (ψ.subst σ).not).not
  rw [subst_not, subst_imp, subst_not]

private theorem inverse_instance_syntax : FOL.substAt (FOL.existsAt 3 (FOL.existsAt 4
    ((mul (.var 10) (.var 3)).equal
      (add (succ zero) (mul (.var 4) (modulus (.var 1) (.var 2))))))) 2 (.var 7) = currentInverse := by
  simp [FOL.substAt, currentInverse, currentInverseBody, modulus,
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

private theorem future_instance_syntax :
    FOL.substAt futureBody 2 (.var 7) =
      (((less (.var 7) (.var 7)).not) ⊓ less (.var 7) (.var 8)).imp currentInverse := by
  have h := inverse_instance_syntax
  unfold FOL.substAt at h ⊢
  simp only [futureBody, subst_imp, subst_and, subst_not, less_subst, h,
    FirstOrder.Language.Term.subst, ↓reduceIte, show (7 : Nat) ≠ 2 by decide,
    show (8 : Nat) ≠ 2 by decide]

/-- Select the current-index inverse from the future-family condition and k<N.
This is an actual PA derivation; no external inverse is chosen. -/
theorem current_inverse_select :
    FormulaProves ((futureAt (.var 7) 10).imp
      ((less (.var 7) (.var 8)).imp currentInverse)) := by
  let F := futureAt (.var 7) 10
  let L := less (.var 7) (.var 8)
  let G := ((less (.var 7) (.var 7)).not) ⊓ L
  have inst : FormulaProves (F.imp (G.imp currentInverse)) := by
    have h := FOL.Derivation.logical (Axiom := Peano.Axiom)
      (FOL.LogicalAxiom.allElim futureBody 2 (.var 7))
    change FormulaProves ((futureAt (.var 7) 10).imp (FOL.substAt futureBody 2 (.var 7))) at h
    simpa only [F, future_instance_syntax, G, L] using h
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hf : FOL.Context Peano.Axiom [L,F] F := FOL.Context.under (FOL.Context.head [] F) L
  have hl : FOL.Context Peano.Axiom [L,F] L := FOL.Context.head _ _
  have hg : FOL.Context Peano.Axiom [L,F] G :=
    FOL.Context.conjunctionIntro (.closed (PeanoOrderIrreflexive.less_self (.var 7))) hl
  exact .mp (.mp (.closed inst) hf) hg

end PASoundness.PeanoBetaCRTSelect.Inverse


/-! Generic FOL existential witness combination for the PA CRT selection. -/
namespace PASoundness.PeanoBetaCRTSelect.Combine
open FirstOrder FirstOrder.Language
open Peano

private theorem fv_inf (φ ψ : Peano.Formula) :
    (φ ⊓ ψ).freeVarFinset = φ.freeVarFinset ∪ ψ.freeVarFinset := by
  change ((φ.imp ψ.not).not).freeVarFinset = _
  simp [FirstOrder.Language.BoundedFormula.freeVarFinset]

private theorem fv_exists (φ : Peano.Formula) (x : Nat) :
    (FOL.existsAt x φ).freeVarFinset = φ.freeVarFinset.erase x := by
  simp [FOL.existsAt, SyntaxTransport.allAt_freeVars,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.freeVarFinset]

/-- Combine independent row and inverse witnesses. The freshness hypotheses
prevent the quantifiers from capturing parameters in the other formula. -/
theorem combine (R I L : Peano.Formula)
    (hR14 : 14 ∉ R.freeVarFinset) (hR15 : 15 ∉ R.freeVarFinset)
    (hL14 : 14 ∉ L.freeVarFinset) (hL15 : 15 ∉ L.freeVarFinset)
    (hI13 : 13 ∉ I.freeVarFinset) : FormulaProves
    ((FOL.existsAt 13 (R ⊓ L)).imp
      ((FOL.existsAt 14 (FOL.existsAt 15 I)).imp
        (FOL.existsAt 13 (FOL.existsAt 14 (FOL.existsAt 15 ((R ⊓ I) ⊓ L)))))) := by
  let Q := R ⊓ L
  let J := FOL.existsAt 14 (FOL.existsAt 15 I)
  let T := FOL.existsAt 13 (FOL.existsAt 14 (FOL.existsAt 15 ((R ⊓ I) ⊓ L)))
  have hi15 : FormulaProves (((R ⊓ I) ⊓ L).imp (FOL.existsAt 15 ((R ⊓ I) ⊓ L))) := by
    simpa only [SyntaxTransport.substAt_self] using
      (FOL.Derivation.existsIntro (A := Peano.Axiom) ((R ⊓ I) ⊓ L) 15 (.var 15))
  have hi14 : FormulaProves ((FOL.existsAt 15 ((R ⊓ I) ⊓ L)).imp
      (FOL.existsAt 14 (FOL.existsAt 15 ((R ⊓ I) ⊓ L)))) := by
    simpa only [SyntaxTransport.substAt_self] using
      (FOL.Derivation.existsIntro (A := Peano.Axiom)
        (FOL.existsAt 15 ((R ⊓ I) ⊓ L)) 14 (.var 14))
  have hi13 : FormulaProves ((FOL.existsAt 14 (FOL.existsAt 15 ((R ⊓ I) ⊓ L))).imp T) := by
    simpa only [T, SyntaxTransport.substAt_self] using
      (FOL.Derivation.existsIntro (A := Peano.Axiom)
        (FOL.existsAt 14 (FOL.existsAt 15 ((R ⊓ I) ⊓ L))) 13 (.var 13))
  have hb : FormulaProves (I.imp (Q.imp T)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    have hI : FOL.Context Peano.Axiom [Q,I] I := FOL.Context.under (FOL.Context.head [] I) Q
    have hQ : FOL.Context Peano.Axiom [Q,I] Q := FOL.Context.head _ _
    have hR := FOL.Context.conjunctionLeft hQ
    have hL := FOL.Context.conjunctionRight hQ
    have hbody := FOL.Context.conjunctionIntro (FOL.Context.conjunctionIntro hR hI) hL
    exact .mp (.closed hi13) (.mp (.closed hi14) (.mp (.closed hi15) hbody))
  have hf15 : 15 ∉ (Q.imp T).freeVarFinset := by
    simp [Q, T, fv_exists, fv_inf, FirstOrder.Language.BoundedFormula.freeVarFinset,
      hR15, hL15]
  have h15 := PeanoBitPositionReduction.exists_elim 15 hf15 hb
  have hf14 : 14 ∉ (Q.imp T).freeVarFinset := by
    simp [Q, T, fv_exists, fv_inf, FirstOrder.Language.BoundedFormula.freeVarFinset,
      hR14, hL14]
  have h14 := PeanoBitPositionReduction.exists_elim 14 hf14 h15
  have hswap : FormulaProves (Q.imp (J.imp T)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    have hQ : FOL.Context Peano.Axiom [J,Q] Q := FOL.Context.under (FOL.Context.head [] Q) J
    have hJ : FOL.Context Peano.Axiom [J,Q] J := FOL.Context.head _ _
    exact .mp (.mp (.closed h14) hJ) hQ
  have hf13 : 13 ∉ (J.imp T).freeVarFinset := by
    simp [J, T, fv_exists, FirstOrder.Language.BoundedFormula.freeVarFinset, hI13]
  exact PeanoBitPositionReduction.exists_elim 13 hf13 hswap
end PASoundness.PeanoBetaCRTSelect.Combine

/-! Fixed-name selection interface. The selected body is the displayed
`((selected φ ⊓ inverseBody) ⊓ bound)` formula. -/
namespace PASoundness.PeanoBetaCRTSelect
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic PeanoDivisibility
open PeanoBetaCRTInvariant

/-- Selected relation under capture-safe simultaneous substitution 2↦7,3↦13. -/
def selected (φ : Peano.Formula) : Peano.Formula :=
  φ.subst (fun x => if x=2 then .var 7 else if x=3 then .var 13 else .var x)

def bound : Peano.Formula := less (.var 13) (modulus (.var 1) (.var 7))
def residueExists (φ : Peano.Formula) : Peano.Formula :=
  FOL.existsAt 13 (selected φ ⊓ bound)

def inverseBody : Peano.Formula :=
  (mul (.var 10) (.var 14)).equal
    (add (succ zero) (mul (.var 15) (modulus (.var 1) (.var 7))))
def inverseExists : Peano.Formula := FOL.existsAt 14 (FOL.existsAt 15 inverseBody)

def selectedBody (φ : Peano.Formula) : Peano.Formula :=
  ((selected φ ⊓ inverseBody) ⊓ bound)
def selectedExists (φ : Peano.Formula) : Peano.Formula :=
  FOL.existsAt 13 (FOL.existsAt 14 (FOL.existsAt 15 (selectedBody φ)))

/-- The selected instance introduces only names 7 and 13. -/
theorem selected_fresh14 (φ : Peano.Formula) (hφ : 14 ∉ φ.freeVarFinset) :
    14 ∉ (selected φ).freeVarFinset := by
  unfold selected
  rw [SyntaxTransport.formula_subst_freeVars]
  rintro ⟨x,hx,hm⟩
  by_cases h2 : x = 2
  · subst x; simp [FirstOrder.Language.Term.varFinset] at hm
  by_cases h3 : x = 3
  · subst x; simp [FirstOrder.Language.Term.varFinset] at hm
  have he' : 14 = x := by
    simpa [h2,h3,FirstOrder.Language.Term.varFinset] using hm
  have he : x = 14 := he'.symm
  subst x
  exact hφ hx

theorem selected_fresh15 (φ : Peano.Formula) (hφ : 15 ∉ φ.freeVarFinset) :
    15 ∉ (selected φ).freeVarFinset := by
  unfold selected
  rw [SyntaxTransport.formula_subst_freeVars]
  rintro ⟨x,hx,hm⟩
  by_cases h2 : x = 2
  · subst x; simp [FirstOrder.Language.Term.varFinset] at hm
  by_cases h3 : x = 3
  · subst x; simp [FirstOrder.Language.Term.varFinset] at hm
  have he' : 15 = x := by
    simpa [h2,h3,FirstOrder.Language.Term.varFinset] using hm
  have he : x = 15 := he'.symm
  subst x
  exact hφ hx

/-- With a supplied bounded residue and k<N, the future-inverse component of
currentMatrix supplies u,v, which PA combines with the same residue witness.
The selected-residue existence itself remains an explicit hypothesis. If name
13 is a free parameter of φ, the residue binder captures that occurrence;
callers needing it independent must also require 13 fresh in φ. -/
theorem select_from_residue (φ : Peano.Formula)
    (hφ14 : 14 ∉ φ.freeVarFinset) (hφ15 : 15 ∉ φ.freeVarFinset) :
    FormulaProves ((residueExists φ).imp ((currentMatrix φ).imp
      ((less (.var 7) (.var 8)).imp (selectedExists φ)))) := by
  let H := residueExists φ
  let C := currentMatrix φ
  let L := less (.var 7) (.var 8)
  let Γ := [L,C,H]
  have hR14 := selected_fresh14 φ hφ14
  have hR15 := selected_fresh15 φ hφ15
  have hL14 : 14 ∉ bound.freeVarFinset := by decide
  have hL15 : 15 ∉ bound.freeVarFinset := by decide
  have hI13 : 13 ∉ inverseBody.freeVarFinset := by decide
  have hmerge := PeanoBetaCRTSelect.Combine.combine (selected φ) inverseBody bound
    hR14 hR15 hL14 hL15 hI13
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hh : FOL.Context Peano.Axiom Γ H := .hypothesis (by simp [Γ])
  have hc : FOL.Context Peano.Axiom Γ C := .hypothesis (by simp [Γ])
  have hl : FOL.Context Peano.Axiom Γ L := FOL.Context.head _ _
  have hf : FOL.Context Peano.Axiom Γ (futureAt (.var 7) 10) :=
    FOL.Context.conjunctionRight hc
  have hi : FOL.Context Peano.Axiom Γ inverseExists := by
    exact FOL.Context.mp (FOL.Context.mp
      (.closed PeanoBetaCRTSelect.Inverse.current_inverse_select) hf) hl
  exact .mp (.mp (.closed hmerge) hh) hi

end PASoundness.PeanoBetaCRTSelect
