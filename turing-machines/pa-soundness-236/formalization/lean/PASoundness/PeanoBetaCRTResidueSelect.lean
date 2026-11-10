import PASoundness.PeanoBetaCRTAlpha
import PASoundness.PeanoBetaCRTSelect
import PASoundness.PeanoBetaCRTAlignment

/-! Selecting a bounded current residue from a supplied totality family. -/
namespace PASoundness.PeanoBetaCRTResidueSelect
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic
open PeanoBetaCRTAlpha

/-- The selected relation is shared with the dependent witness module. -/
abbrev selected := PeanoBetaCRTSelect.selected

def totality (φ : Peano.Formula) : Peano.Formula := FOL.allAt 2
  ((less (.var 2) (.var 8)).imp (FOL.existsAt 3
    (φ ⊓ less (.var 3) (modulus (.var 1) (.var 2)))))

/-- This is the explicit residue hypothesis consumed by CRTSelect. -/
abbrev currentResidue := PeanoBetaCRTSelect.residueExists

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := rfl

private theorem subst_inf (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ ⊓ ψ).subst σ = (φ.subst σ) ⊓ (ψ.subst σ) := by
  change (φ.imp ψ.not).not.subst σ = ((φ.subst σ).imp (ψ.subst σ).not).not
  rfl

private theorem selected_two_subst (φ : Peano.Formula) :
    FOL.substAt (FOL.substAt φ 2 (.var 7)) 3 (.var 13) = selected φ := by
  unfold FOL.substAt selected
  rw [SyntaxTransport.formula_subst_comp]
  congr 1
  funext x
  by_cases h2 : x = 2
  · subst x; simp [FirstOrder.Language.Term.subst]
  · by_cases h3 : x = 3
    · subst x; simp [FirstOrder.Language.Term.subst]
    · simp [h2,h3,FirstOrder.Language.Term.subst]

private theorem target_subst (φ : Peano.Formula) :
    FOL.substAt ((FOL.substAt φ 2 (.var 7)) ⊓
      less (.var 3) (modulus (.var 1) (.var 7))) 3 (.var 13) =
      (selected φ ⊓ less (.var 13) (modulus (.var 1) (.var 7))) := by
  unfold FOL.substAt at *
  simp only [subst_inf, less_subst, modulus, succ_subst, mul_subst,
    FirstOrder.Language.Term.subst, ↓reduceIte, show (1 : Nat) ≠ 3 by decide,
    show (7 : Nat) ≠ 3 by decide]
  exact congrArg₂ (· ⊓ ·) (by simpa only [FOL.substAt] using selected_two_subst φ) rfl

private theorem body_fresh13 (φ : Peano.Formula) (hφ13 : 13 ∉ φ.freeVarFinset) :
    13 ∉ ((FOL.substAt φ 2 (.var 7)) ⊓
      less (.var 3) (modulus (.var 1) (.var 7))).freeVarFinset := by
  have hsel : 13 ∉ (FOL.substAt φ 2 (.var 7)).freeVarFinset := by
    unfold FOL.substAt
    rw [SyntaxTransport.formula_subst_freeVars]
    rintro ⟨z,hz,hm⟩
    by_cases hz2 : z = 2
    · subst z
      simp [FirstOrder.Language.Term.varFinset] at hm
    · have h13 : 13 = z := by simpa [hz2, FirstOrder.Language.Term.varFinset] using hm
      subst z
      exact hφ13 hz
  have hb : 13 ∉ (less (.var 3) (modulus (.var 1) (.var 7))).freeVarFinset := by decide
  change 13 ∉ (((FOL.substAt φ 2 (.var 7)).imp
    (less (.var 3) (modulus (.var 1) (.var 7))).not).not).freeVarFinset
  simp [FirstOrder.Language.BoundedFormula.freeVarFinset, hsel, hb]

/-- PA derives a selected bounded residue from the totality family and k<N.
Name 7 is required fresh in φ to reserve the selected index as a bound index;
name 13 is fresh to avoid capture of relation parameters in the witness binder. -/
theorem select_residue (φ : Peano.Formula)
    (_hφ7 : 7 ∉ φ.freeVarFinset) (hφ13 : 13 ∉ φ.freeVarFinset) :
    FormulaProves ((totality φ).imp ((less (.var 7) (.var 8)).imp (currentResidue φ))) := by
  let B := φ ⊓ less (.var 3) (modulus (.var 1) (.var 2))
  let J := FOL.substAt φ 2 (.var 7) ⊓ less (.var 3) (modulus (.var 1) (.var 7))
  have hinst : FormulaProves ((totality φ).imp ((less (.var 7) (.var 8)).imp
      (FOL.existsAt 3 J))) := by
    have h := FOL.Derivation.logical (Axiom := Peano.Axiom)
      (FOL.LogicalAxiom.allElim ((less (.var 2) (.var 8)).imp (FOL.existsAt 3 B)) 2 (.var 7))
    have hex : FOL.substAt (FOL.existsAt 3 B) 2 (.var 7) = FOL.existsAt 3 J := by
      rw [subst_var_existsAt _ 2 7 3 (by decide) (by decide)]
      unfold J B FOL.substAt
      simp only [subst_inf, less_subst, modulus, succ_subst, mul_subst,
        FirstOrder.Language.Term.subst, ↓reduceIte, show (3 : Nat) ≠ 2 by decide,
        show (1 : Nat) ≠ 2 by decide]
    have he : FOL.substAt ((less (.var 2) (.var 8)).imp (FOL.existsAt 3 B)) 2 (.var 7) =
        ((less (.var 7) (.var 8)).imp (FOL.existsAt 3 J)) := by
      unfold FOL.substAt at *
      simp only [subst_imp, less_subst, hex, FirstOrder.Language.Term.subst,
        ↓reduceIte, show (8 : Nat) ≠ 2 by decide]
    simpa only [totality, he] using h
  have hrename := exists_alpha_forward J 3 13 (by decide) (body_fresh13 φ hφ13)
  have hrename' : FormulaProves ((FOL.existsAt 3 J).imp (currentResidue φ)) := by
    simpa only [J, currentResidue, PeanoBetaCRTSelect.residueExists,
      PeanoBetaCRTSelect.bound, target_subst] using hrename
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have ht : FOL.Context Peano.Axiom [less (.var 7) (.var 8),totality φ] (totality φ) :=
    FOL.Context.under (FOL.Context.head [] _) (less (.var 7) (.var 8))
  have hl : FOL.Context Peano.Axiom [less (.var 7) (.var 8),totality φ]
      (less (.var 7) (.var 8)) := FOL.Context.head _ _
  exact .mp (.closed hrename') (.mp (.mp (.closed hinst) ht) hl)

/-- The chosen local condition is exactly the aligned row update's side
condition, with the identical conjunction order and witness names. -/
theorem selected_body_alignment (φ : Peano.Formula) :
    PeanoBetaCRTSelect.selectedBody φ = PeanoBetaCRTAlignment.rowAssumptions φ := by
  rfl

/-- The selected local witness formula expected by the dependent-state wrapper
binds residue 13 followed by inverse witnesses 14 and 15. -/
theorem selected_exists_alignment (φ : Peano.Formula) :
    PeanoBetaCRTSelect.selectedExists φ = FOL.existsAt 13 (FOL.existsAt 14
      (FOL.existsAt 15 (PeanoBetaCRTAlignment.rowAssumptions φ))) := by
  rfl

/-- Bounded relation totality and k<N yield all three selected witnesses
inside the exposed current state. The current inverse comes from the state's
future clause; no inverse or residue witness is chosen semantically. -/
theorem select_from_totality (φ : Peano.Formula)
    (hφ7 : 7 ∉ φ.freeVarFinset) (hφ13 : 13 ∉ φ.freeVarFinset)
    (hφ14 : 14 ∉ φ.freeVarFinset) (hφ15 : 15 ∉ φ.freeVarFinset) :
    FormulaProves ((totality φ).imp ((less (.var 7) (.var 8)).imp
      ((PeanoBetaCRTInvariant.currentMatrix φ).imp (PeanoBetaCRTSelect.selectedExists φ)))) := by
  let T := totality φ
  let L := less (.var 7) (.var 8)
  let C := PeanoBetaCRTInvariant.currentMatrix φ
  let Γ := [C,L,T]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have ht : FOL.Context Peano.Axiom Γ T := .hypothesis (by simp [Γ])
  have hl : FOL.Context Peano.Axiom Γ L := .hypothesis (by simp [Γ])
  have hc : FOL.Context Peano.Axiom Γ C := FOL.Context.head _ _
  have hr : FOL.Context Peano.Axiom Γ (PeanoBetaCRTSelect.residueExists φ) :=
    .mp (.mp (.closed (select_residue φ hφ7 hφ13)) ht) hl
  exact .mp (.mp (.mp (.closed (PeanoBetaCRTSelect.select_from_residue φ hφ14 hφ15))
    hr) hc) hl

/-- Alignment's reserved-name convention supplies the selection freshness. -/
theorem select_from_totality_namesSafe (φ : Peano.Formula)
    (hφ : PeanoBetaCRTAlignment.NamesSafe φ) :
    FormulaProves ((totality φ).imp ((less (.var 7) (.var 8)).imp
      ((PeanoBetaCRTInvariant.currentMatrix φ).imp (PeanoBetaCRTSelect.selectedExists φ)))) := by
  have hf7 : 7 ∉ φ.freeVarFinset := by
    intro h; have hx := hφ 7 h; simp [PeanoBetaCRTAlignment.reservedNames] at hx
  have hf13 : 13 ∉ φ.freeVarFinset := by
    intro h; have hx := hφ 13 h; simp [PeanoBetaCRTAlignment.reservedNames] at hx
  have hf14 : 14 ∉ φ.freeVarFinset := by
    intro h; have hx := hφ 14 h; simp [PeanoBetaCRTAlignment.reservedNames] at hx
  have hf15 : 15 ∉ φ.freeVarFinset := by
    intro h; have hx := hφ 15 h; simp [PeanoBetaCRTAlignment.reservedNames] at hx
  exact select_from_totality φ hf7 hf13 hf14 hf15

/-- Global input condition: the relation has a bounded value at each index
below N, and the current index k is still below N. -/
def assumptions (φ : Peano.Formula) : Peano.Formula :=
  totality φ ⊓ less (.var 7) (.var 8)

private theorem fv_inf (φ ψ : Peano.Formula) :
    (φ ⊓ ψ).freeVarFinset = φ.freeVarFinset ∪ ψ.freeVarFinset := by
  change ((φ.imp ψ.not).not).freeVarFinset = _
  simp [FirstOrder.Language.BoundedFormula.freeVarFinset]

private theorem fv_exists (φ : Peano.Formula) (x : Nat) :
    (FOL.existsAt x φ).freeVarFinset = φ.freeVarFinset.erase x := by
  simp [FOL.existsAt, SyntaxTransport.allAt_freeVars,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.freeVarFinset]

/-- The chosen relation substitutions introduce only names 7 and 13. -/
theorem selected_fresh (φ : Peano.Formula) (x : Nat)
    (hx7 : x ≠ 7) (hx13 : x ≠ 13) (hφ : x ∉ φ.freeVarFinset) :
    x ∉ (selected φ).freeVarFinset := by
  unfold selected PeanoBetaCRTSelect.selected
  rw [SyntaxTransport.formula_subst_freeVars]
  rintro ⟨y,hy,hm⟩
  by_cases h2 : y = 2
  · subst y
    simp [FirstOrder.Language.Term.varFinset, hx7] at hm
  · by_cases h3 : y = 3
    · subst y
      simp [FirstOrder.Language.Term.varFinset, hx13] at hm
    · have heq : x = y := by
        simpa [h2, h3, FirstOrder.Language.Term.varFinset] using hm
      exact hφ (heq ▸ hy)

/-- Names other than the displayed fixed variables are fresh in totality and
k<N if they were fresh in the target relation. -/
theorem assumptions_fresh (φ : Peano.Formula) (x : Nat)
    (hx1 : x ≠ 1) (hx2 : x ≠ 2) (hx3 : x ≠ 3)
    (hx7 : x ≠ 7) (hx8 : x ≠ 8) (hφ : x ∉ φ.freeVarFinset) :
    x ∉ (assumptions φ).freeVarFinset := by
  have h1 : (less (.var 2) (.var 8)).freeVarFinset = {2,8} := by decide
  have h2 : (less (.var 3) (modulus (.var 1) (.var 2))).freeVarFinset = {1,2,3} := by decide
  have h3 : (less (.var 7) (.var 8)).freeVarFinset = {7,8} := by decide
  simp [assumptions, totality, fv_inf, fv_exists, SyntaxTransport.allAt_freeVars,
    FirstOrder.Language.BoundedFormula.freeVarFinset, h1, h2, h3,
    hx1, hx2, hx3, hx7, hx8, hφ]

/-- Existential residue selection introduces no other free names. -/
theorem residue_fresh (φ : Peano.Formula) (x : Nat)
    (hx1 : x ≠ 1) (hx7 : x ≠ 7) (hx13 : x ≠ 13)
    (hφ : x ∉ φ.freeVarFinset) : x ∉ (PeanoBetaCRTSelect.residueExists φ).freeVarFinset := by
  have hs := selected_fresh φ x hx7 hx13 hφ
  have hb : PeanoBetaCRTSelect.bound.freeVarFinset = {1,7,13} := by decide
  simp [PeanoBetaCRTSelect.residueExists, fv_exists, fv_inf, hb, hs, hx1, hx7, hx13]

/-- In the exposed old state, the global condition supplies exactly the
selected local side condition of the aligned row update, with witnesses
13,14,15. No CRT component update is claimed. -/
theorem selected_exists_in_state (φ : Peano.Formula)
    (hφ : PeanoBetaCRTAlignment.NamesSafe φ) :
    FormulaProves ((assumptions φ).imp ((PeanoBetaCRTInvariant.currentMatrix φ).imp
      (FOL.existsAt 13 (FOL.existsAt 14 (FOL.existsAt 15
        (PeanoBetaCRTAlignment.rowAssumptions φ)))))) := by
  let A := assumptions φ
  let C := PeanoBetaCRTInvariant.currentMatrix φ
  let Γ := [C,A]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have ha : FOL.Context Peano.Axiom Γ A := FOL.Context.under (FOL.Context.head [] A) C
  have hc : FOL.Context Peano.Axiom Γ C := FOL.Context.head _ _
  have ht : FOL.Context Peano.Axiom Γ (totality φ) := FOL.Context.conjunctionLeft ha
  have hl : FOL.Context Peano.Axiom Γ (less (.var 7) (.var 8)) := FOL.Context.conjunctionRight ha
  have hs := FOL.Context.mp (FOL.Context.mp (FOL.Context.mp
    (.closed (select_from_totality_namesSafe φ hφ)) ht) hl) hc
  simpa only [selected_exists_alignment] using hs

end PASoundness.PeanoBetaCRTResidueSelect
