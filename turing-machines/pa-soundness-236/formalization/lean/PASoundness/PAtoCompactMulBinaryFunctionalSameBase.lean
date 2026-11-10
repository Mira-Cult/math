import PASoundness.PAtoCompactMulBinaryFunctionalGuarded
import PASoundness.PAtoCompactAllTermTransport

/-! Multiplication graph functionality at the same caller base, from two
explicit child-functionality proofs at a fresh second private base. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMulBinaryFunctionalSameBase

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermSubstBinaryStep
open PASoundness.PAtoCompactAllTermTransport PASoundness.PAtoCompactMulBinaryFunctionalGuarded

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

noncomputable def mul_functionality_same_base {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (b c p q e f : Nat) (g : Formula)
    (hbc : b+1 < c) (hp : p < b) (hq : q < b)
    (ht : ∀ a ∈ t.varFinset, v a < b) (hu : ∀ a ∈ u.varFinset, v a < b)
    (hg : ∀ a ∈ g.free, a < b)
    (hbe : b + 1 < e + 2) (hce : c + 1 < e + 2)
    (hpf : p < f + 2) (hqf : q < f + 2)
    (left : KDerivation (imp g.encode
      (imp (termGraph v t b (b+64)).encode
        (imp (termGraph v t c (c+64)).encode (equivAt e b c).encode))))
    (right : KDerivation (imp g.encode
      (imp (termGraph v u (b+1) (b+64+termCost t)).encode
        (imp (termGraph v u (c+1) (c+64+termCost t)).encode
          (equivAt e (b+1) (c+1)).encode)))) :
    KDerivation (imp g.encode
      (imp (termGraph v (binaryTerm false t u) p b).encode
        (imp (termGraph v (binaryTerm false t u) q b).encode (equivAt f p q).encode))) := by
  let s := binaryTerm false t u
  have hvars : ∀ a ∈ s.varFinset, v a < b := by
    intro a ha
    simp only [s, binaryTerm, Bool.false_eq_true, ↓reduceIte, Term.varFinset,
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
  have h := mul_functionality_fresh v t u b c p q e f g hbc hp hq ht hu hg
    hbe hce hpf hqf left right
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(termGraph v s q b).encode,(termGraph v s p b).encode,g.encode]
  have hq₀ : Context Γ (termGraph v s q b).encode := .head _ _
  have hp₀ : Context Γ (termGraph v s p b).encode := .hypothesis (by simp [Γ])
  have hg₀ : Context Γ g.encode := .hypothesis (by simp [Γ])
  have hq₁ := Context.mp hq₀ (.closed htransport)
  simpa [Γ, s] using Context.mp hq₁ (Context.mp hp₀ (Context.mp hg₀ (.closed h)))

theorem mul_functionality_same_base_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (b c p q e f : Nat) (g : Formula)
    (hbc : b+1 < c) (hp : p < b) (hq : q < b)
    (ht : ∀ a ∈ t.varFinset, v a < b) (hu : ∀ a ∈ u.varFinset, v a < b)
    (hg : ∀ a ∈ g.free, a < b)
    (hbe : b + 1 < e + 2) (hce : c + 1 < e + 2)
    (hpf : p < f + 2) (hqf : q < f + 2)
    (left : KDerivation (imp g.encode
      (imp (termGraph v t b (b+64)).encode
        (imp (termGraph v t c (c+64)).encode (equivAt e b c).encode))))
    (right : KDerivation (imp g.encode
      (imp (termGraph v u (b+1) (b+64+termCost t)).encode
        (imp (termGraph v u (c+1) (c+64+termCost t)).encode
          (equivAt e (b+1) (c+1)).encode)))) :
    theoremCode (certificate (mul_functionality_same_base v t u b c p q e f g hbc hp hq ht hu hg
      hbe hce hpf hqf left right)) =
      imp g.encode (imp (termGraph v (binaryTerm false t u) p b).encode
        (imp (termGraph v (binaryTerm false t u) q b).encode (equivAt f p q).encode)) := certificate_correct _

end PASoundness.PAtoCompactMulBinaryFunctionalSameBase

#print axioms PASoundness.PAtoCompactMulBinaryFunctionalSameBase.mul_functionality_same_base
#print axioms PASoundness.PAtoCompactMulBinaryFunctionalSameBase.mul_functionality_same_base_certificate
