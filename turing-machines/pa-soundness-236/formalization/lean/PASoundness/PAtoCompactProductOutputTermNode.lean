import PASoundness.PAtoCompactProductOutputDynamic
import PASoundness.PAtoCompactTermZeroGuarded
import PASoundness.PAtoCompactSuccGraphOutputLift
import PASoundness.PAtoCompactFreeNames

/-! Product-node term-graph output transport. The source-domain guard is
projected from the actual supplied source graph, and the target-domain guard
and output equivalence remain explicit. The original child witnesses are
reused; no graph functionality or recursive output theorem is assumed. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputTermNode

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermZeroGuarded
open PASoundness.PAtoCompactSuccGraphOutputLift PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactProductOutputDynamic

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The actual source graph supplies domain(q); the target domain and q≈r
remain separate object-level hypotheses. -/
noncomputable def mul_output_lift {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (b q r : Nat)
    (hq : q < b) (hr : r < b)
    (hv : ∀ a ∈ (binaryTerm false t u).varFinset, v a < b) :
    KDerivation (imp (domainAt b r).encode
      (imp (termGraph v (binaryTerm false t u) q b).encode
        (imp (equivAt b q r).encode (termGraph v (binaryTerm false t u) r b).encode))) := by
  let G := andF (domainAt b q) (andF (domainAt b r) (equivAt b q r))
  let L := termGraph v t b (b+64)
  let R := termGraph v u (b+1) (b+64+termCost t)
  let M := andF L (andF R (binaryRel false b b (b+1) q))
  let T := termGraph v (binaryTerm false t u) r b
  have hG (k : Nat) (hk : b ≤ k) : k ∉ G.free := by
    intro h
    simp only [G, andF_free, Finset.mem_union] at h
    rcases h with hdq | hdr | he
    · have hh := domainAt_free b q hdq
      simp only [Finset.mem_singleton] at hh
      omega
    · have hh := domainAt_free b r hdr
      simp only [Finset.mem_singleton] at hh
      omega
    · have hh := equivAt_free b q r he
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with hh | hh <;> omega
  have hT (k : Nat) (hk : b ≤ k) : k ∉ T.free := by
    intro h
    have hh := termGraph_free_subset v (binaryTerm false t u) r b h
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hh
    rcases hh with ⟨a, ha, he⟩ | he
    · have ha' := hv a ha
      omega
    · omega
  have introGraph := binary_from_witness v false t u b r
  have hop := guarded_output b b (b+1) q r (by omega) (by omega) (by omega) (by omega)
  have hpoint : KDerivation (imp G.encode (imp M.encode T.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [M.encode,G.encode]
    have hg0 : Context Γ G.encode := .hypothesis (by simp [Γ])
    have hm0 : Context Γ M.encode := .head _ _
    have hg : Context Γ (both (domainAt b q).encode
        (both (domainAt b r).encode (equivAt b q r).encode)) := by
      simpa [G, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hg0
    have hm : Context Γ (both L.encode (both R.encode (binaryRel false b b (b+1) q).encode)) := by
      simpa [M, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hm0
    have hdq := Context.conjunctionLeft hg
    have hdr := Context.conjunctionLeft (Context.conjunctionRight hg)
    have he := Context.conjunctionRight (Context.conjunctionRight hg)
    have hl := Context.conjunctionLeft hm
    have hr' := Context.conjunctionLeft (Context.conjunctionRight hm)
    have hrel := Context.conjunctionRight (Context.conjunctionRight hm)
    have hrel' : Context Γ (binaryRel false b b (b+1) r).encode := by
      have h := Context.mp hdq (Context.mp he (Context.mp hrel (.closed hop)))
      simpa [binaryRel, PAtoCompactProductOutputFixedBase.frame, CompactNamed.Formula.encode] using h
    exact .mp hrel' (.mp hr' (.mp hl (.mp hdr (.closed introGraph))))
  have inner := guarded_exists_left (b+1) G.encode M.encode T.encode
    (free_vacuity (b+1) G (hG (b+1) (by omega)))
    (free_vacuity (b+1) T (hT (b+1) (by omega))) hpoint
  have outer := guarded_exists_left b G.encode (existsCode (b+1) M.encode) T.encode
    (free_vacuity b G (hG b (by omega)))
    (free_vacuity b T (hT b (by omega))) inner
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(equivAt b q r).encode,(termGraph v (binaryTerm false t u) q b).encode,(domainAt b r).encode]
  have he : Context Γ (equivAt b q r).encode := .head _ _
  have hs : Context Γ (termGraph v (binaryTerm false t u) q b).encode := .hypothesis (by simp [Γ])
  have hd : Context Γ (domainAt b r).encode := .hypothesis (by simp [Γ])
  have hs' : Context Γ (both (domainAt b q).encode (existsCode b (existsCode (b+1) M.encode))) := by
    simpa [binaryTerm, binaryRel, termGraph, M, L, R, andF,
      CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg, existsCode] using hs
  have hg : Context Γ G.encode := by
    simpa [G, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro (Context.conjunctionLeft hs') (Context.conjunctionIntro hd he)
  exact .mp (Context.conjunctionRight hs') (.mp hg (.closed outer))

theorem mul_output_lift_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (b q r : Nat) (hq : q < b) (hr : r < b)
    (hv : ∀ a ∈ (binaryTerm false t u).varFinset, v a < b) :
    theoremCode (certificate (mul_output_lift v t u b q r hq hr hv)) =
      imp (domainAt b r).encode (imp (termGraph v (binaryTerm false t u) q b).encode
        (imp (equivAt b q r).encode (termGraph v (binaryTerm false t u) r b).encode)) := certificate_correct _

end PASoundness.PAtoCompactProductOutputTermNode

#print axioms PASoundness.PAtoCompactProductOutputTermNode.mul_output_lift
#print axioms PASoundness.PAtoCompactProductOutputTermNode.mul_output_lift_certificate
