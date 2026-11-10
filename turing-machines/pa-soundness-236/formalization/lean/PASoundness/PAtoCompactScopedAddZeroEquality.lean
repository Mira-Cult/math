import PASoundness.PAtoCompactGuardedArbitraryTermFrames
import PASoundness.PAtoCompactScopedSubstitutedEqualityShape
import PASoundness.PAtoCompactSuccSubstSyntax
import PASoundness.PAtoCompactVacuousQuantifierFree
import PASoundness.PAtoCompactGuardedLogicalCongruence
import PASoundness.PAtoCompactTermSubstPolyReplacement

/-! A scoped equality adapter under a fixed retained hypothesis. The two
term-graph alignment inputs are finite K proofs at all sufficiently high
allocators; no graph existence or substitution property is assumed implicitly.
Free source names and bound levels remain distinct until interpretation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactScopedAddZeroEquality
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactBoundSubstInterpret PASoundness.PAtoCompactSuccSubstSyntax
open PASoundness.PAtoCompactScopedSubstitutedEqualityShape PASoundness.PAtoCompactVacuousQuantifierFree
open PASoundness.PAtoCompactScopedEqualityReplace PASoundness.PAtoCompactGuardedLogicalCongruence
open PASoundness.PAtoCompactGuardedArbitraryTermFrames PASoundness.PAtoCompactTermSubstInduction
open PASoundness.PAtoCompactTermSubstPolyReplacement

/-- Equality frames align under H when the two interpreted term graphs align
under that same H at any allocator above their names and H's free support. -/
noncomputable def scoped_equal_of_graph_align {n : Nat}
    (H : Formula) (σ τ : Nat → Peano.Term)
    (s t : Peano.language.Term (Nat ⊕ Fin n)) (bound : Fin n → Nat)
    (left : ∀ b out, out < b → (∀ a ∈ H.free, a < b) →
      (∀ a ∈ (s.subst (Sum.elim σ (Term.var ∘ bound))).varFinset, a < b) →
      (∀ a ∈ (s.subst (Sum.elim τ (Term.var ∘ bound))).varFinset, a < b) →
      Align H (s.subst (Sum.elim σ (Term.var ∘ bound)))
        (s.subst (Sum.elim τ (Term.var ∘ bound))) b out)
    (right : ∀ b out, out < b → (∀ a ∈ H.free, a < b) →
      (∀ a ∈ (t.subst (Sum.elim σ (Term.var ∘ bound))).varFinset, a < b) →
      (∀ a ∈ (t.subst (Sum.elim τ (Term.var ∘ bound))).varFinset, a < b) →
      Align H (t.subst (Sum.elim σ (Term.var ∘ bound)))
        (t.subst (Sum.elim τ (Term.var ∘ bound))) b out) :
    GuardedBoth H
      (scopedFormula n ((.equal s t : Peano.language.BoundedFormula Nat n).subst σ) bound)
      (scopedFormula n ((.equal s t : Peano.language.BoundedFormula Nat n).subst τ) bound) := by
  let a₁ := s.subst (Sum.elim σ (Term.var ∘ bound))
  let a₂ := t.subst (Sum.elim σ (Term.var ∘ bound))
  let b₁ := s.subst (Sum.elim τ (Term.var ∘ bound))
  let b₂ := t.subst (Sum.elim τ (Term.var ∘ bound))
  let F : Peano.language.BoundedFormula Nat n := .equal s t
  let vbase := scopeBase (F.subst σ) bound
  let sbase := scopeBase (F.subst τ) bound
  let high := max (comparisonBase F σ τ bound) (H.free.sup id + 1)
  have hv₁ : ∀ a ∈ a₁.varFinset, a < vbase := by
    intro a ha
    apply left_substituted_names_lt s t σ bound a
    rw [interpret_subst]
    exact ha
  have hv₂ : ∀ a ∈ a₂.varFinset, a < vbase := by
    intro a ha
    apply right_substituted_names_lt s t σ bound a
    rw [interpret_subst]
    exact ha
  have hs₁ : ∀ a ∈ b₁.varFinset, a < sbase := by
    intro a ha
    apply left_substituted_names_lt s t τ bound a
    rw [interpret_subst]
    exact ha
  have hs₂ : ∀ a ∈ b₂.varFinset, a < sbase := by
    intro a ha
    apply right_substituted_names_lt s t τ bound a
    rw [interpret_subst]
    exact ha
  have hvle : vbase ≤ high := by dsimp [high, comparisonBase, vbase]; omega
  have hsle : sbase ≤ high := by dsimp [high, comparisonBase, sbase]; omega
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
  have hleft : Align H a₁ b₁ (high+2) high := by
    apply left (high+2) high (by omega)
    · intro a ha; have := hHhigh a ha; omega
    · intro a ha; have hh : a < high := hv₁h a ha; omega
    · intro a ha; have hh : a < high := hs₁h a ha; omega
  have hright : Align H a₂ b₂ (high+2+termCost a₁) (high+1) := by
    apply right (high+2+termCost a₁) (high+1) (by omega)
    · intro a ha; have := hHhigh a ha; omega
    · intro a ha; have hh : a < high := hv₂h a ha; omega
    · intro a ha; have hh : a < high := hs₂h a ha; omega
  have halign := guarded_frame_alignment H a₁ a₂ b₁ b₂ high hHhigh hs₂h hleft hright
  have shapeV : scopedFormula n (F.subst σ) bound = equalityFrame id a₁ a₂ vbase := by
    rw [scoped_substituted_equality_shape s t σ bound]
  have shapeS : scopedFormula n (F.subst τ) bound = equalityFrame id b₁ b₂ sbase := by
    rw [scoped_substituted_equality_shape s t τ bound]
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

/-- Scoped equality alignment for any replacement with the two displayed
finite K graph laws. Source tags distinguish free variables from bound
levels even when their interpreted labels alias. -/
noncomputable def scoped_equal_of_replacement {n : Nat}
    (g : Formula) (replacement : Peano.Term) (x q d : Nat)
    (hqd : q < d) (htd : ∀ a ∈ replacement.varFinset, a < d)
    (hdom : ∀ a ∈ replacement.varFinset,
      KDerivation (imp g.encode (domainAt d a).encode))
    (output : OutputTransport replacement) (functional : GuardFunctionality g replacement)
    (s t : Peano.language.Term (Nat ⊕ Fin n)) (bound : Fin n → Nat) :
    GuardedBoth (retained g replacement q d)
      (scopedFormula n ((.equal s t : Peano.language.BoundedFormula Nat n).subst
        (singleSubst x (.var q))) bound)
      (scopedFormula n ((.equal s t : Peano.language.BoundedFormula Nat n).subst
        (singleSubst x replacement)) bound) := by
  classical
  let σ := singleSubst x (.var q)
  let τ := singleSubst x replacement
  let select : Nat ⊕ Fin n → Prop := fun a => a = Sum.inl x
  let name : Nat ⊕ Fin n → Nat := Sum.elim id bound
  let mapσ : Nat ⊕ Fin n → Peano.Term := fun a => if select a then .var q else .var (name a)
  let mapτ : Nat ⊕ Fin n → Peano.Term := fun a => if select a then replacement else .var (name a)
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
  apply scoped_equal_of_graph_align (retained g replacement q d) σ τ s t bound
  · intro b out hout hH hs ht
    rw [heσ] at hs
    rw [heτ] at ht
    rw [heσ, heτ]
    exact selected_substitution select name g replacement q d hqd htd hdom output functional
      s b out hout hH hs ht
  · intro b out hout hH hs ht
    rw [heσ] at hs
    rw [heτ] at ht
    rw [heσ, heτ]
    exact selected_substitution select name g replacement q d hqd htd hdom output functional
      t b out hout hH hs ht

end PASoundness.PAtoCompactScopedAddZeroEquality

#print axioms PASoundness.PAtoCompactScopedAddZeroEquality.scoped_equal_of_graph_align
#print axioms PASoundness.PAtoCompactScopedAddZeroEquality.scoped_equal_of_replacement
