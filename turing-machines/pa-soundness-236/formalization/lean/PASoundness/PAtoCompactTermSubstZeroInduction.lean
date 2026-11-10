import PASoundness.PAtoCompactTermSubstPolymorphic

/-! Structural zero substitution for arbitrary decidable source names, with
the finite K zero-variable leaf left explicit. The source type may distinguish
free names from bound levels even when their target names alias. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactTermSubstZeroInduction

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactHilbertBasis PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactTermSubstPolymorphic

def retainedZero (g : Formula) (q d : Nat) : Formula :=
  andF g (termGraph id Peano.zero q d)

/-- Construct both term-graph substitution directions for every source term
from the explicit zero-variable leaf. Unselected source variables use their
mapped names, with no injectivity or target-name freshness assumption. -/
noncomputable def selected_zero_substitution
    {α : Type} [DecidableEq α] (selected : α → Prop) [DecidablePred selected]
    (name : α → Nat) (g : Formula) (q d : Nat)
    (zeroLeaf : ∀ b out, out < b → q < b →
      (∀ a ∈ (retainedZero g q d).free, a < b) →
      Align (retainedZero g q d) (.var q) Peano.zero b out)
    (s : Peano.language.Term α) (b out : Nat) (hout : out < b)
    (hH : ∀ a ∈ (retainedZero g q d).free, a < b)
    (hs : ∀ a ∈ (s.subst (fun a => if selected a then .var q else .var (name a))).varFinset, a < b)
    (ht : ∀ a ∈ (s.subst (fun a => if selected a then Peano.zero else .var (name a))).varFinset, a < b) :
    Align (retainedZero g q d)
      (s.subst (fun a => if selected a then .var q else .var (name a)))
      (s.subst (fun a => if selected a then Peano.zero else .var (name a))) b out := by
  let σ : α → Peano.Term := fun a => if selected a then .var q else .var (name a)
  let τ : α → Peano.Term := fun a => if selected a then Peano.zero else .var (name a)
  apply term_subst_align (retainedZero g q d) σ τ s
  · intro a ha base result hr hH' hσ hτ
    by_cases hsel : selected a
    · have hq : q < base := by apply hσ q; simp [σ, hsel, Term.varFinset]
      simp only [σ, τ, hsel, ↓reduceIte]
      exact zeroLeaf base result hr hq hH'
    · simp only [σ, τ, hsel, ↓reduceIte]
      let X := (termGraph id (.var (name a) : Peano.Term) result base).encode
      have wk : KDerivation (imp (imp X X) (imp (retainedZero g q d).encode (imp X X))) :=
        weakening _ _
      have hi : KDerivation (imp (retainedZero g q d).encode (imp X X)) := .mp (identity _) wk
      exact ⟨hi, hi⟩
  · exact hout
  · exact hH
  · exact hs
  · exact ht

end PASoundness.PAtoCompactTermSubstZeroInduction

#print axioms PASoundness.PAtoCompactTermSubstZeroInduction.selected_zero_substitution
