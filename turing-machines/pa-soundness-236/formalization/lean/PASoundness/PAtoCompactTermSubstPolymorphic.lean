import PASoundness.PAtoCompactTermSubstSuccStep
import PASoundness.PAtoCompactTermSubstBinaryStep
import PASoundness.PAtoCompactAllTermTransport
import PASoundness.SyntaxTransport

/-! Polymorphic-source term-graph substitution by structural induction.
The source variable type may separate free names from active bound levels;
finite K alignments at the source term's actual leaves remain explicit. -/
namespace PASoundness.PAtoCompactTermSubstPolymorphic

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactHilbertBasis PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactAllTermTransport

set_option maxRecDepth 65536
set_option maxHeartbeats 0

abbrev Align (H : Formula) (s t : Peano.Term) (b out : Nat) : Type :=
  KDerivation (imp H.encode (imp (termGraph id s out b).encode (termGraph id t out b).encode)) ×
  KDerivation (imp H.encode (imp (termGraph id t out b).encode (termGraph id s out b).encode))

/-- Only the source term's actual variable leaves require compatibility.
Each variable of either substituted term and each free guard name must be
strictly below the graph allocation base; the output must be below it as well. -/
def LeafAlign {α : Type} [DecidableEq α] (H : Formula) (σ τ : α → Peano.Term) (s : Peano.language.Term α) : Type :=
  ∀ a ∈ s.varFinset, ∀ b out,
    out < b → (∀ v ∈ H.free, v < b) →
    (∀ v ∈ (σ a).varFinset, v < b) →
    (∀ v ∈ (τ a).varFinset, v < b) → Align H (σ a) (τ a) b out

noncomputable def term_subst_align {α : Type} [DecidableEq α] (H : Formula) (σ τ : α → Peano.Term) (s : Peano.language.Term α) :
    LeafAlign H σ τ s → ∀ b out,
    out < b → (∀ v ∈ H.free, v < b) →
    (∀ v ∈ (s.subst σ).varFinset, v < b) →
    (∀ v ∈ (s.subst τ).varFinset, v < b) →
    Align H (s.subst σ) (s.subst τ) b out := by
  induction s with
  | var a =>
    intro leaf b out hout hH hs ht
    exact leaf a (by simp [Term.varFinset]) b out hout hH (by simpa [Term.subst] using hs)
      (by simpa [Term.subst] using ht)
  | @func l sym ts ih =>
    intro leaf b out hout hH hs ht
    have hleaf (i : Fin l) : LeafAlign H σ τ (ts i) := by
      intro a ha
      apply leaf a
      simp only [Term.varFinset, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨i, ha⟩
    have hschild (i : Fin l) : ∀ v ∈ ((ts i).subst σ).varFinset, v < b := by
      intro v hv
      apply hs v
      simp only [Term.subst, Term.varFinset, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨i, hv⟩
    have htchild (i : Fin l) : ∀ v ∈ ((ts i).subst τ).varFinset, v < b := by
      intro v hv
      apply ht v
      simp only [Term.subst, Term.varFinset, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨i, hv⟩
    cases sym with
    | zero =>
      have hts : ts = Fin.elim0 := by funext i; exact Fin.elim0 i
      subst ts
      change Align H (Peano.zero) (Peano.zero) b out
      have d := weakening (imp (termGraph id Peano.zero out b).encode
        (termGraph id Peano.zero out b).encode) H.encode
      have di : KDerivation (imp H.encode (imp (termGraph id Peano.zero out b).encode
          (termGraph id Peano.zero out b).encode)) := .mp (identity _) d
      exact ⟨di, di⟩
    | succ =>
      have child := ih 0 (hleaf 0) (b+64) b (by omega)
        (by intro v hv; have := hH v hv; omega)
        (by intro v hv; have := hschild 0 v hv; omega)
        (by intro v hv; have := htchild 0 v hv; omega)
      have hv := free_vacuity b H (by intro hb; have := hH b hb; omega)
      have d := PASoundness.PAtoCompactTermSubstSuccStep.succ_both id id
        ((ts 0).subst σ) ((ts 0).subst τ) b out H hv child.1 child.2
      have hσ : ![(ts 0).subst σ] = (fun i => (ts i).subst σ) := by
        funext i; fin_cases i; rfl
      have hτ : ![(ts 0).subst τ] = (fun i => (ts i).subst τ) := by
        funext i; fin_cases i; rfl
      simpa only [Align, Term.subst, PASoundness.PAtoCompactTermSubstSuccStep.succTerm, hσ, hτ] using d
    | add | mul =>
      let ls := (ts 0).subst σ
      let lt := (ts 0).subst τ
      let rs := (ts 1).subst σ
      let rt := (ts 1).subst τ
      let bs := b + 64 + termCost ls
      let bt := b + 64 + termCost lt
      have left := ih 0 (hleaf 0) (b+64) b (by omega)
        (by intro v hv; have := hH v hv; omega)
        (by intro v hv; have := hschild 0 v hv; omega)
        (by intro v hv; have := htchild 0 v hv; omega)
      have right := ih 1 (hleaf 1) bs (b+1) (by dsimp [bs]; omega)
        (by intro v hv; have := hH v hv; dsimp [bs]; omega)
        (by intro v hv; have := hschild 1 v hv; dsimp [bs]; omega)
        (by intro v hv; have := htchild 1 v hv; dsimp [bs]; omega)
      have tr := termGraph_base_transport id rt bs bt (b+1)
        (by dsimp [bs]; omega) (by dsimp [bt]; omega)
        (by intro v hv; have := htchild 1 v hv; dsimp [bs]; omega)
        (by intro v hv; have := htchild 1 v hv; dsimp [bt]; omega)
      have r1 := compose right.1 (implicationCongr (identity _) tr.1)
      have r2 := compose right.2 (implicationCongr tr.2 (identity _))
      have hv0 := free_vacuity b H (by intro hb; have := hH b hb; omega)
      have hv1 := free_vacuity (b+1) H (by intro hb; have := hH (b+1) hb; omega)
      have hσ : ![(ts 0).subst σ, (ts 1).subst σ] =
          (fun i => (ts i).subst σ) := by funext i; fin_cases i <;> rfl
      have hτ : ![(ts 0).subst τ, (ts 1).subst τ] =
          (fun i => (ts i).subst τ) := by funext i; fin_cases i <;> rfl
      first
      | case add =>
          have d := PASoundness.PAtoCompactTermSubstBinaryStep.binary_both id id true
            ls rs lt rt b out H hv0 hv1 left.1 left.2 r1 r2
          simpa only [Align, Term.subst, PASoundness.PAtoCompactTermSubstBinaryStep.binaryTerm,
            Bool.true_eq_false, ↓reduceIte, ls, lt, rs, rt, hσ, hτ] using d
      | case mul =>
          have d := PASoundness.PAtoCompactTermSubstBinaryStep.binary_both id id false
            ls rs lt rt b out H hv0 hv1 left.1 left.2 r1 r2
          simpa only [Align, Term.subst, PASoundness.PAtoCompactTermSubstBinaryStep.binaryTerm,
            Bool.false_eq_true, ↓reduceIte, ls, lt, rs, rt, hσ, hτ] using d

end PASoundness.PAtoCompactTermSubstPolymorphic

#print axioms PASoundness.PAtoCompactTermSubstPolymorphic.term_subst_align
