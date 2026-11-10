import PASoundness.PAtoCompactTermSubstPolymorphic
import PASoundness.PAtoCompactTermSubstSuccessorInduction

/-! Successor substitution at a selected set of source variables of arbitrary
decidable type. Unselected source variables map through an arbitrary target
name map, which can identify distinct source labels. This keeps free names
and bound levels distinct at the source even if target names alias. -/
namespace PASoundness.PAtoCompactTermSubstPolySuccessor
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactHilbertBasis PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactUnaryTermTransport PASoundness.PAtoCompactTermSubstPolymorphic
open PASoundness.PAtoCompactTermSubstSuccessorInduction PASoundness.PAtoCompactFreeNames

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Structural successor substitution for any source-variable type. The
selection predicate identifies variables to replace, while all other source
variables retain their possibly aliased mapped target name. -/
noncomputable def selected_successor_substitution
    {α : Type} [DecidableEq α] (selected : α → Prop) [DecidablePred selected]
    (name : α → Nat) (g : Formula) (u : Peano.Term) (hu : UnaryTerm u)
    (q d : Nat) (hqd : q < d) (hud : ∀ a ∈ u.varFinset, a < d)
    (hdom : ∀ a ∈ u.varFinset, KDerivation (imp g.encode (domainAt d a).encode))
    (s : Peano.language.Term α) (b out : Nat) (hout : out < b)
    (hH : ∀ a ∈ (retained g u q d).free, a < b)
    (hs : ∀ a ∈ (s.subst (fun a => if selected a then .var q else .var (name a))).varFinset, a < b)
    (ht : ∀ a ∈ (s.subst (fun a => if selected a then succTerm u else .var (name a))).varFinset, a < b) :
    Align (retained g u q d)
      (s.subst (fun a => if selected a then .var q else .var (name a)))
      (s.subst (fun a => if selected a then succTerm u else .var (name a))) b out := by
  let σ : α → Peano.Term := fun a => if selected a then .var q else .var (name a)
  let τ : α → Peano.Term := fun a => if selected a then succTerm u else .var (name a)
  apply term_subst_align (retained g u q d) σ τ s
  · intro a ha base result hr hH' hσ hτ
    by_cases hsel : selected a
    · have hq : q < base := by apply hσ q; simp [σ, hsel, Term.varFinset]
      have hbu : ∀ v ∈ u.varFinset, v < base := by
        intro v hv
        apply hτ v
        simpa [τ, hsel, succTerm, Term.varFinset] using hv
      have hbg : ∀ v ∈ g.free, v < base := by
        intro v hv
        apply hH' v
        rw [retained, andF_free]
        exact Finset.mem_union_left _ hv
      simp only [σ, τ, hsel, ↓reduceIte]
      exact successor_leaf g u hu q d base result hqd hq hr hud hbu hbg hdom
    · simp only [σ, τ, hsel, ↓reduceIte]
      let X := (termGraph id (.var (name a) : Peano.Term) result base).encode
      have wk : KDerivation (imp (imp X X) (imp (retained g u q d).encode (imp X X))) :=
        weakening _ _
      have hi : KDerivation (imp (retained g u q d).encode (imp X X)) := .mp (identity _) wk
      exact ⟨hi, hi⟩
  · exact hout
  · exact hH
  · exact hs
  · exact ht

end PASoundness.PAtoCompactTermSubstPolySuccessor

#print axioms PASoundness.PAtoCompactTermSubstPolySuccessor.selected_successor_substitution
