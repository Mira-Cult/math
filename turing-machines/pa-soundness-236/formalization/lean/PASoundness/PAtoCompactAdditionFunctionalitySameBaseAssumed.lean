import PASoundness.PAtoCompactAllTermTransport
import PASoundness.PAtoCompactTermSubstBinaryStep

/-! Move the second input of a supplied guarded addition-graph functionality
implication to the caller's graph base. The fresh-base implication is an
explicit finite K proof input; this file does not establish addition
functionality or any arithmetic axiom. -/

set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionFunctionalitySameBaseAssumed

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermSubstBinaryStep
open PASoundness.PAtoCompactAllTermTransport

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The two parent outputs may alias, as may the source variable labels. The
source implication itself is supplied; only its second graph is transported. -/
noncomputable def same_base {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (b c p q f : Nat) (g : Formula)
    (hbc : b < c) (hp : p < b) (hq : q < b)
    (ht : ∀ a ∈ t.varFinset, v a < b) (hu : ∀ a ∈ u.varFinset, v a < b)
    (fresh : KDerivation (imp g.encode
      (imp (termGraph v (binaryTerm true t u) p b).encode
        (imp (termGraph v (binaryTerm true t u) q c).encode (equivAt f p q).encode)))) :
    KDerivation (imp g.encode
      (imp (termGraph v (binaryTerm true t u) p b).encode
        (imp (termGraph v (binaryTerm true t u) q b).encode (equivAt f p q).encode))) := by
  let s := binaryTerm true t u
  have hvars : ∀ a ∈ s.varFinset, v a < b := by
    intro a ha
    simp only [s, binaryTerm, Bool.true_eq_false, ↓reduceIte, Term.varFinset,
      Finset.mem_biUnion, Finset.mem_univ, true_and] at ha
    obtain ⟨i, hi⟩ := ha
    fin_cases i
    · exact ht a hi
    · exact hu a hi
  have hvars' : ∀ a ∈ s.varFinset, v a < c := by
    intro a ha
    have h := hvars a ha
    omega
  have htransport := (termGraph_base_transport v s b c q hq (by omega) hvars hvars').1
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(termGraph v s q b).encode, (termGraph v s p b).encode, g.encode]
  have hq₀ : Context Γ (termGraph v s q b).encode := .head _ _
  have hp₀ : Context Γ (termGraph v s p b).encode := .hypothesis (by simp [Γ])
  have hg₀ : Context Γ g.encode := .hypothesis (by simp [Γ])
  have hq₁ := Context.mp hq₀ (.closed htransport)
  simpa [Γ, s] using Context.mp hq₁ (Context.mp hp₀ (Context.mp hg₀ (.closed fresh)))

theorem same_base_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (b c p q f : Nat) (g : Formula)
    (hbc : b < c) (hp : p < b) (hq : q < b)
    (ht : ∀ a ∈ t.varFinset, v a < b) (hu : ∀ a ∈ u.varFinset, v a < b)
    (fresh : KDerivation (imp g.encode
      (imp (termGraph v (binaryTerm true t u) p b).encode
        (imp (termGraph v (binaryTerm true t u) q c).encode (equivAt f p q).encode)))) :
    theoremCode (certificate (same_base v t u b c p q f g hbc hp hq ht hu fresh)) =
      imp g.encode (imp (termGraph v (binaryTerm true t u) p b).encode
        (imp (termGraph v (binaryTerm true t u) q b).encode (equivAt f p q).encode)) :=
  certificate_correct _

end PASoundness.PAtoCompactAdditionFunctionalitySameBaseAssumed

#print axioms PASoundness.PAtoCompactAdditionFunctionalitySameBaseAssumed.same_base
#print axioms PASoundness.PAtoCompactAdditionFunctionalitySameBaseAssumed.same_base_certificate
