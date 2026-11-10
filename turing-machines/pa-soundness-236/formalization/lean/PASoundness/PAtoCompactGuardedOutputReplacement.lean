import PASoundness.PAtoCompactTermSubstPolymorphic
import PASoundness.PAtoCompactSuccTermTotality
import PASoundness.PAtoCompactGuardBaseTransport
import PASoundness.PAtoCompactTermSubstPolyReplacement
import PASoundness.PAtoCompactVariableGraphLaws

/-! Draft guard-conditioned selected-variable term substitution. This keeps
the source candidate obligations explicit. No graph law or PA bridge is
asserted without its stated finite K proof inputs. -/
namespace PASoundness.PAtoCompactGuardedOutputReplacement

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactHilbertBasis PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactTermSubstPolymorphic PASoundness.PAtoCompactAllTermTransport
open PASoundness.PAtoCompactSuccTermTotality PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactTermSubstPolyReplacement
open PASoundness.PAtoCompactVariableGraphLaws

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Output replacement, conditional on the guard actually providing candidate
conditions for all variables occurring in the term. All listed requirements
are explicit finite K proof inputs, not semantic assumptions. -/
def GuardedOutputTransport (g : Formula) (t : Peano.Term) : Type :=
  ∀ b q r, q < b → r < b → (∀ a ∈ t.varFinset, a < b) →
    (∀ a ∈ g.free, a < b) →
    (∀ a ∈ t.varFinset, KDerivation (imp g.encode (domainAt b a).encode)) →
    KDerivation (imp g.encode (imp (domainAt b r).encode
      (imp (termGraph id t q b).encode
        (imp (equivAt b q r).encode (termGraph id t r b).encode))))

/-- Existing unguarded output laws imply the guarded interface. -/
def guard_unguarded_output (g : Formula) (t : Peano.Term)
    (h : OutputTransport t) : GuardedOutputTransport g t := by
  intro b q r hq hr ht _ _
  exact KDerivation.mp (h b q r hq hr ht) (weakening _ _)

/-- Variable output transport with the source-candidate guard retained.
This does not infer candidatehood from a graph or from an isomorphism. -/
def variable_output (g : Formula) (a : Nat) : GuardedOutputTransport g (.var a) := by
  intro b q r hq hr hv _ hd
  have ha : a < b := hv a (by simp [Term.varFinset])
  have hdom : KDerivation (imp g.encode (domainAt b a).encode) :=
    hd a (by simp [Term.varFinset])
  have hvout := variable_output_forward id a b q r (by simp only [id_eq]; omega)
    (by omega) (by omega)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let G := (termGraph id (.var a : Peano.Term) q b).encode
  let E := (equivAt b q r).encode
  let D := (domainAt b r).encode
  let Γ := [E,G,D,g.encode]
  have he : Context Γ E := .head _ _
  have hgraph : Context Γ G := .hypothesis (by simp [Γ])
  have hD : Context Γ D := .hypothesis (by simp [Γ])
  have hg : Context Γ g.encode := .hypothesis (by simp [Γ])
  have haD : Context Γ (domainAt b a).encode := .mp hg (.closed hdom)
  have hqr : Context Γ (termGraph id (.var q : Peano.Term) r b).encode :=
    Context.conjunctionIntro hD he
  exact .mp hqr (.mp hgraph (.mp haD (.closed hvout)))

/-- The selected-variable leaf. Both graph laws are explicit, as are the
guard's candidate proofs at the retained graph's base. -/
noncomputable def replacement_leaf (g : Formula) (t : Peano.Term)
    (q d b out : Nat) (hqd : q < d) (hq : q < b) (hout : out < b)
    (htd : ∀ a ∈ t.varFinset, a < d) (htb : ∀ a ∈ t.varFinset, a < b)
    (hg : ∀ a ∈ g.free, a < b)
    (hdom : ∀ a ∈ t.varFinset, KDerivation (imp g.encode (domainAt d a).encode))
    (output : GuardedOutputTransport g t) (functional : GuardFunctionality g t) :
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
  have ho := output b q out hq hout htb hg hbdom
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
    exact .mp hE (.mp hGb (.mp hD (.mp (Context.conjunctionLeft hH) (.closed ho))))
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
    (output : GuardedOutputTransport g t) (functional : GuardFunctionality g t)
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

end PASoundness.PAtoCompactGuardedOutputReplacement

#print axioms PASoundness.PAtoCompactGuardedOutputReplacement.replacement_leaf
#print axioms PASoundness.PAtoCompactGuardedOutputReplacement.selected_substitution
