import PASoundness.PAtoCompactProductMatchOperationGuarded
import PASoundness.PAtoCompactBinaryGraphFunctionalFresh

/-! Guarded multiplication term-graph functionality from the two child
functionality proofs. The source-output domain is extracted from the first
actual graph and supplied to multiplication congruence. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMulBinaryFunctionalGuarded

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermSubstBinaryStep
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactBinaryGraphFunctionalFresh
open PASoundness.PAtoCompactProductMatchOperationGuarded

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Two child graph-functionality proofs imply multiplication graph
functionality, with the original guard unchanged. -/
noncomputable def mul_functionality_fresh {α : Type} [DecidableEq α] (v : α → Nat)
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
        (imp (termGraph v (binaryTerm false t u) q c).encode (equivAt f p q).encode))) := by
  let G := andF g (domainAt b p)
  have hGfree : ∀ a ∈ G.free, a < b := by
    intro a ha
    simp only [G, andF_free, Finset.mem_union] at ha
    rcases ha with ha | ha
    · exact hg a ha
    · have he := domainAt_free b p ha
      simp only [Finset.mem_singleton] at he
      omega
  have left' : KDerivation (imp G.encode
      (imp (termGraph v t b (b+64)).encode
        (imp (termGraph v t c (c+64)).encode (equivAt e b c).encode))) := by
    apply Context.closeEmpty
    apply Context.deduction
    have h : Context [G.encode] (both g.encode (domainAt b p).encode) := by
      simpa [G, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using (Context.head [] G.encode)
    exact Context.mp (Context.conjunctionLeft h) (.closed left)
  have right' : KDerivation (imp G.encode
      (imp (termGraph v u (b+1) (b+64+termCost t)).encode
        (imp (termGraph v u (c+1) (c+64+termCost t)).encode (equivAt e (b+1) (c+1)).encode))) := by
    apply Context.closeEmpty
    apply Context.deduction
    have h : Context [G.encode] (both g.encode (domainAt b p).encode) := by
      simpa [G, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using (Context.head [] G.encode)
    exact Context.mp (Context.conjunctionLeft h) (.closed right)
  have hop : KDerivation (imp G.encode
      (imp (equivAt e b c).encode (imp (equivAt e (b+1) (c+1)).encode
        (imp (binaryRel false b p).encode (imp (binaryRel false c q).encode (equivAt f p q).encode))))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Γ := [(binaryRel false c q).encode,(binaryRel false b p).encode,
      (equivAt e (b+1) (c+1)).encode,(equivAt e b c).encode,G.encode]
    have hm₂ : Context Γ (binaryRel false c q).encode := .head _ _
    have hm₁ : Context Γ (binaryRel false b p).encode := .hypothesis (by simp [Γ])
    have he₂ : Context Γ (equivAt e (b+1) (c+1)).encode := .hypothesis (by simp [Γ])
    have he₁ : Context Γ (equivAt e b c).encode := .hypothesis (by simp [Γ])
    have hg : Context Γ G.encode := .hypothesis (by simp [Γ])
    have hg' : Context Γ (both g.encode (domainAt b p).encode) := by
      simpa [G, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hg
    have h := Context.mp hm₂ (Context.mp hm₁ (Context.mp he₂ (Context.mp he₁
      (Context.mp (Context.conjunctionRight hg')
        (.closed (operation_guarded b c p q e f (by omega) (by omega) hbe hce hpf hqf))))))
    simpa [Γ, binaryRel] using h
  have hstrong := binary_functionality_fresh v t u false b c p q e f G
    hbc hp hq ht hu hGfree left' right' hop
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let A := termGraph v (binaryTerm false t u) p b
  let B := termGraph v (binaryTerm false t u) q c
  let Γ := [B.encode,A.encode,g.encode]
  have hb : Context Γ B.encode := .head _ _
  have ha : Context Γ A.encode := .hypothesis (by simp [Γ])
  have hg₀ : Context Γ g.encode := .hypothesis (by simp [Γ])
  have ha' : Context Γ (both (domainAt b p).encode
      (existsCode b (existsCode (b+1) (matrix v false t u b p).encode))) := by
    simpa [A, binaryTerm, termGraph, matrix, binaryRel, andF, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, both, neg, existsCode] using ha
  have hG : Context Γ G.encode := by
    simpa [G, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro hg₀ (Context.conjunctionLeft ha')
  simpa [Γ, A, B] using Context.mp hb (Context.mp ha (Context.mp hG (.closed hstrong)))

theorem mul_functionality_fresh_certificate {α : Type} [DecidableEq α] (v : α → Nat)
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
    theoremCode (certificate (mul_functionality_fresh v t u b c p q e f g hbc hp hq ht hu hg
      hbe hce hpf hqf left right)) =
      imp g.encode (imp (termGraph v (binaryTerm false t u) p b).encode
        (imp (termGraph v (binaryTerm false t u) q c).encode (equivAt f p q).encode)) := certificate_correct _

end PASoundness.PAtoCompactMulBinaryFunctionalGuarded

#print axioms PASoundness.PAtoCompactMulBinaryFunctionalGuarded.mul_functionality_fresh
#print axioms PASoundness.PAtoCompactMulBinaryFunctionalGuarded.mul_functionality_fresh_certificate
