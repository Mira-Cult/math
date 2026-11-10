import PASoundness.PAtoCompactGuardedArbitraryTermFrames
import PASoundness.PAtoCompactTermSubstZeroClosed
import PASoundness.PAtoCompactScopedSubstitutedEqualityShape
import PASoundness.PAtoCompactSuccSubstSyntax
import PASoundness.PAtoCompactVacuousQuantifierFree
import PASoundness.PAtoCompactGuardedLogicalCongruence

/-! Capture-avoiding zero substitution through a scoped PA equality.
Free variables and bound levels remain distinct until after substitution;
active interpreted labels may alias. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactScopedZeroEqualityFull
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactBoundSubstInterpret
open PASoundness.PAtoCompactSuccSubstSyntax
open PASoundness.PAtoCompactGuardedArbitraryTermFrames PASoundness.PAtoCompactScopedSubstitutedEqualityShape
open PASoundness.PAtoCompactTermSubstZeroClosed PASoundness.PAtoCompactTermSubstZeroInduction
open PASoundness.PAtoCompactVacuousQuantifierFree PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactGuardedLogicalCongruence PASoundness.SyntaxTransport

/-- Both K implications through a scoped equality, under the retained guard.
The retained guard contains the displayed zero graph, and no K proof-data
inputs are supplied. No injectivity or freshness condition is imposed on
the active bound-level name map. -/
noncomputable def scoped_zero_equal {n : Nat}
    (g : Formula) (x q d : Nat) (hqd : q < d)
    (s t : Peano.language.Term (Nat ⊕ Fin n)) (bound : Fin n → Nat) :
    let H := retainedZero g q d
    let σ := singleSubst x (.var q)
    let τ := singleSubst x (Peano.zero)
    GuardedBoth H (scopedFormula n ((.equal s t : Peano.language.BoundedFormula Nat n).subst σ) bound)
      (scopedFormula n ((.equal s t : Peano.language.BoundedFormula Nat n).subst τ) bound) := by
  classical
  dsimp only
  let H := retainedZero g q d
  let σ := singleSubst x (.var q)
  let τ := singleSubst x (Peano.zero)
  let select : Nat ⊕ Fin n → Prop := fun a => a = Sum.inl x
  let name : Nat ⊕ Fin n → Nat := Sum.elim id bound
  let mapσ : Nat ⊕ Fin n → Peano.Term := fun a => if select a then .var q else .var (name a)
  let mapτ : Nat ⊕ Fin n → Peano.Term := fun a => if select a then Peano.zero else .var (name a)
  have heσ : Sum.elim σ (Term.var ∘ bound) = mapσ := by
    funext a
    cases a with
    | inl a => simp [σ, singleSubst, mapσ, select, name]
    | inr i => simp [σ, mapσ, select, name]
  have heτ : Sum.elim τ (Term.var ∘ bound) = mapτ := by
    funext a
    cases a with
    | inl a => simp [τ, singleSubst, mapτ, select, name]
    | inr i => simp [τ, mapτ, select, name]
  let a₁ := s.subst mapσ
  let a₂ := t.subst mapσ
  let b₁ := s.subst mapτ
  let b₂ := t.subst mapτ
  let F : Peano.language.BoundedFormula Nat n := .equal s t
  let vbase := scopeBase (F.subst σ) bound
  let sbase := scopeBase (F.subst τ) bound
  let cmp := comparisonBase F σ τ bound
  let high := max cmp (H.free.sup id + 1)
  have hv₁ : ∀ a ∈ a₁.varFinset, a < vbase := by
    intro a ha
    apply left_substituted_names_lt s t σ bound a
    rw [interpret_subst, heσ]
    exact ha
  have hv₂ : ∀ a ∈ a₂.varFinset, a < vbase := by
    intro a ha
    apply right_substituted_names_lt s t σ bound a
    rw [interpret_subst, heσ]
    exact ha
  have hs₁ : ∀ a ∈ b₁.varFinset, a < sbase := by
    intro a ha
    apply left_substituted_names_lt s t τ bound a
    rw [interpret_subst, heτ]
    exact ha
  have hs₂ : ∀ a ∈ b₂.varFinset, a < sbase := by
    intro a ha
    apply right_substituted_names_lt s t τ bound a
    rw [interpret_subst, heτ]
    exact ha
  have hvle : vbase ≤ high := by dsimp [high, cmp, comparisonBase, vbase]; omega
  have hsle : sbase ≤ high := by dsimp [high, cmp, comparisonBase, sbase]; omega
  have hv₁h : ∀ a ∈ a₁.varFinset, id a < high := by intro a ha; simp only [id_eq]; have := hv₁ a ha; omega
  have hv₂h : ∀ a ∈ a₂.varFinset, id a < high := by intro a ha; simp only [id_eq]; have := hv₂ a ha; omega
  have hs₁h : ∀ a ∈ b₁.varFinset, id a < high := by intro a ha; simp only [id_eq]; have := hs₁ a ha; omega
  have hs₂h : ∀ a ∈ b₂.varFinset, id a < high := by intro a ha; simp only [id_eq]; have := hs₂ a ha; omega
  have hHhigh : ∀ a ∈ H.free, a < high := by
    intro a ha
    have hh : a ≤ H.free.sup id := Finset.le_sup (f := id) ha
    dsimp [high]
    omega
  have hvtr := equalityFrame_base_transport id a₁ a₂ vbase high hv₁ hv₂ hv₁h hv₂h
  have hstr := equalityFrame_base_transport id b₁ b₂ sbase high hs₁ hs₂ hs₁h hs₂h
  have hleft := selected_zero_substitution_closed select name g q d hqd s (high+2) high
    (by omega) (by intro a ha; have := hHhigh a ha; omega)
    (by intro a ha; have := hv₁ a ha; omega)
    (by intro a ha; have := hs₁ a ha; omega)
  have hright := selected_zero_substitution_closed select name g q d hqd t (high+2+termCost a₁) (high+1)
    (by omega) (by intro a ha; have := hHhigh a ha; omega)
    (by intro a ha; have := hv₂ a ha; omega)
    (by intro a ha; have := hs₂ a ha; omega)
  have halign := guarded_frame_alignment H a₁ a₂ b₁ b₂ high hHhigh
    (by intro a ha; simpa only [id_eq] using hs₂h a ha)
    (by simpa only [a₁, b₁, mapσ, mapτ] using hleft)
    (by simpa only [a₂, b₂, mapσ, mapτ] using hright)
  have shapeV : scopedFormula n (F.subst σ) bound = equalityFrame id a₁ a₂ vbase := by
    rw [scoped_substituted_equality_shape s t σ bound, heσ]
  have shapeS : scopedFormula n (F.subst τ) bound = equalityFrame id b₁ b₂ sbase := by
    rw [scoped_substituted_equality_shape s t τ bound, heτ]
  rw [shapeV, shapeS]
  constructor
  · apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [(equalityFrame id a₁ a₂ vbase).encode,H.encode]
    have hv : Context Γ (equalityFrame id a₁ a₂ vbase).encode := Context.head _ _
    have hg : Context Γ H.encode := .hypothesis (by simp [Γ])
    exact .mp (.mp (.mp hv (.closed hvtr.1)) (.mp hg (.closed halign.1))) (.closed hstr.2)
  · apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [(equalityFrame id b₁ b₂ sbase).encode,H.encode]
    have hs : Context Γ (equalityFrame id b₁ b₂ sbase).encode := Context.head _ _
    have hg : Context Γ H.encode := .hypothesis (by simp [Γ])
    exact .mp (.mp (.mp hs (.closed hstr.1)) (.mp hg (.closed halign.2))) (.closed hvtr.2)

end PASoundness.PAtoCompactScopedZeroEqualityFull

#print axioms PASoundness.PAtoCompactScopedZeroEqualityFull.scoped_zero_equal
