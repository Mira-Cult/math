import PASoundness.PAtoCompactTermSubstPolymorphic
import PASoundness.PAtoCompactSuccTermTotality
import PASoundness.PAtoCompactGuardBaseTransport

/-! Selected-variable term substitution from explicit graph laws. The
retained witness and guard are fixed. Neither graph output transport nor
functionality is assumed to hold without its finite K proof input. -/
namespace PASoundness.PAtoCompactTermSubstPolyReplacement

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactHilbertBasis PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactTermSubstPolymorphic PASoundness.PAtoCompactAllTermTransport
open PASoundness.PAtoCompactSuccTermTotality PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactFreeNames

set_option maxRecDepth 65536
set_option maxHeartbeats 0

def retained (g : Formula) (t : Peano.Term) (q d : Nat) : Formula :=
  andF g (termGraph id t q d)

/-- A per-base finite K output transport law for the chosen term graph. -/
def OutputTransport (t : Peano.Term) : Type :=
  ∀ b q r, q < b → r < b → (∀ a ∈ t.varFinset, a < b) →
    KDerivation (imp (domainAt b r).encode
      (imp (termGraph id t q b).encode
        (imp (equivAt b q r).encode (termGraph id t r b).encode)))

/-- Guarded finite K functionality at each eligible base and output pair. -/
def GuardFunctionality (g : Formula) (t : Peano.Term) : Type :=
  ∀ b q r, q < b → r < b → (∀ a ∈ t.varFinset, a < b) →
    (∀ a ∈ g.free, a < b) →
    (∀ a ∈ t.varFinset, KDerivation (imp g.encode (domainAt b a).encode)) →
    KDerivation (imp g.encode (imp (termGraph id t q b).encode
      (imp (termGraph id t r b).encode (equivAt b q r).encode)))

/-- The selected-variable leaf. Both graph laws are explicit, as are the
guard's candidate proofs at the retained graph's base. -/
noncomputable def replacement_leaf (g : Formula) (t : Peano.Term)
    (q d b out : Nat) (hqd : q < d) (hq : q < b) (hout : out < b)
    (htd : ∀ a ∈ t.varFinset, a < d) (htb : ∀ a ∈ t.varFinset, a < b)
    (hg : ∀ a ∈ g.free, a < b)
    (hdom : ∀ a ∈ t.varFinset, KDerivation (imp g.encode (domainAt d a).encode))
    (output : OutputTransport t) (functional : GuardFunctionality g t) :
    Align (retained g t q d) (.var q) t b out := by
  let H := retained g t q d
  let G := (termGraph id t q d).encode
  let Gb := (termGraph id t q b).encode
  let V := (termGraph id (.var q : Peano.Term) out b).encode
  let T := (termGraph id t out b).encode
  have hmove := (termGraph_base_transport id t d b q hqd hq htd htb).1
  have hbdom (a : Nat) (ha : a ∈ t.varFinset) :
      KDerivation (imp g.encode (domainAt b a).encode) :=
    compose (hdom a ha) (domainAt_transport d b a (by have := htd a ha; omega)
      (by have := htb a ha; omega))
  have ho := output b q out hq hout htb
  have hf := functional b q out hq hout htb hg hbdom
  have hgt := termGraph_domain id t out b
  constructor
  · apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [V, H.encode]
    have hH : Context Γ (both g.encode G) := by
      have hh : Context Γ H.encode := .hypothesis (by simp [Γ])
      simpa [H, retained, G, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hh
    have hV : Context Γ V := Context.head _ _
    have hGb : Context Γ Gb := .mp (Context.conjunctionRight hH) (.closed hmove)
    have hD : Context Γ (domainAt b out).encode := Context.conjunctionLeft hV
    have hE : Context Γ (equivAt b q out).encode := Context.conjunctionRight hV
    exact .mp hE (.mp hGb (.mp hD (.closed ho)))
  · apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [T, H.encode]
    have hH : Context Γ (both g.encode G) := by
      have hh : Context Γ H.encode := .hypothesis (by simp [Γ])
      simpa [H, retained, G, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hh
    have hT : Context Γ T := Context.head _ _
    have hGb : Context Γ Gb := .mp (Context.conjunctionRight hH) (.closed hmove)
    have hD : Context Γ (domainAt b out).encode := .mp hT (.closed hgt)
    have hE : Context Γ (equivAt b q out).encode :=
      .mp hT (.mp hGb (.mp (Context.conjunctionLeft hH) (.closed hf)))
    exact Context.conjunctionIntro hD hE

/-- Arbitrary source-variable tags and a decidable selection predicate
preserve bound/free provenance, even when interpreted labels coincide. -/
noncomputable def selected_substitution
    {α : Type} [DecidableEq α] (selected : α → Prop) [DecidablePred selected]
    (name : α → Nat) (g : Formula) (t : Peano.Term)
    (q d : Nat) (hqd : q < d) (htd : ∀ a ∈ t.varFinset, a < d)
    (hdom : ∀ a ∈ t.varFinset, KDerivation (imp g.encode (domainAt d a).encode))
    (output : OutputTransport t) (functional : GuardFunctionality g t)
    (s : Peano.language.Term α) (b out : Nat) (hout : out < b)
    (hH : ∀ a ∈ (retained g t q d).free, a < b)
    (hs : ∀ a ∈ (s.subst (fun a => if selected a then .var q else .var (name a))).varFinset, a < b)
    (ht : ∀ a ∈ (s.subst (fun a => if selected a then t else .var (name a))).varFinset, a < b) :
    Align (retained g t q d)
      (s.subst (fun a => if selected a then .var q else .var (name a)))
      (s.subst (fun a => if selected a then t else .var (name a))) b out := by
  let σ : α → Peano.Term := fun a => if selected a then .var q else .var (name a)
  let τ : α → Peano.Term := fun a => if selected a then t else .var (name a)
  apply term_subst_align (retained g t q d) σ τ s
  · intro a ha base result hr hH' hσ hτ
    by_cases hsel : selected a
    · have hq : q < base := by apply hσ q; simp [σ, hsel, Term.varFinset]
      have htb : ∀ v ∈ t.varFinset, v < base := by
        intro v hv
        apply hτ v
        simpa [τ, hsel] using hv
      have hbg : ∀ v ∈ g.free, v < base := by
        intro v hv
        apply hH' v
        rw [retained, andF_free]
        exact Finset.mem_union_left _ hv
      simp only [σ, τ, hsel, ↓reduceIte]
      exact replacement_leaf g t q d base result hqd hq hr htd htb hbg hdom output functional
    · simp only [σ, τ, hsel, ↓reduceIte]
      let X := (termGraph id (.var (name a) : Peano.Term) result base).encode
      have wk : KDerivation (imp (imp X X) (imp (retained g t q d).encode (imp X X))) :=
        weakening _ _
      have hi : KDerivation (imp (retained g t q d).encode (imp X X)) := .mp (identity _) wk
      exact ⟨hi, hi⟩
  · exact hout
  · exact hH
  · exact hs
  · exact ht

end PASoundness.PAtoCompactTermSubstPolyReplacement

#print axioms PASoundness.PAtoCompactTermSubstPolyReplacement.replacement_leaf
#print axioms PASoundness.PAtoCompactTermSubstPolyReplacement.selected_substitution
