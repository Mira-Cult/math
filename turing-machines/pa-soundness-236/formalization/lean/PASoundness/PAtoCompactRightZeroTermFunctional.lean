import PASoundness.PAtoCompactRightZeroTermGrammar
import PASoundness.PAtoCompactTermSubstAddZeroLeaf

/-! Guarded graph functionality for unary terms repeatedly wrapped in +0.
Candidate proofs and allocator/name bounds are explicit; aliases are allowed. -/
namespace PASoundness.PAtoCompactRightZeroTermFunctional

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactUnaryTermTransport
open PASoundness.PAtoCompactTermZeroGuarded PASoundness.PAtoCompactRightZeroTermGrammar
open PASoundness.PAtoCompactTermSubstAddZeroLeaf PASoundness.PAtoCompactAllTermTransport
open PASoundness.PAtoCompactEquivMultiAlpha PASoundness.PAtoCompactAddZeroGraphFunctionalClosed
open PASoundness.PAtoCompactUnaryGraphFunctionalityFull PASoundness.PAtoCompactGuardBaseTransport

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] PASoundness.CompactProof.imp Cantor.pair Cantor.triangle

/-- The same child-functionality interface as the unary proof, preserved
when zero is added on the right. -/
noncomputable def add_zero_step {α : Type} [DecidableEq α] (v : α → Nat)
    (g : Formula) (u : Peano.language.Term α)
    (ih : ∀ b p q, (∀ a ∈ u.varFinset, v a < b) → (∀ x ∈ g.free, x < b) →
      (∀ a ∈ u.varFinset, KDerivation (imp g.encode (domainAt b (v a)).encode)) →
      p < b → q < b → KDerivation (imp g.encode (imp (termGraph v u p b).encode
        (imp (termGraph v u q b).encode (equivAt b p q).encode)))) :
    ∀ b p q, (∀ a ∈ (addZero u).varFinset, v a < b) → (∀ x ∈ g.free, x < b) →
      (∀ a ∈ (addZero u).varFinset, KDerivation (imp g.encode (domainAt b (v a)).encode)) →
      p < b → q < b → KDerivation (imp g.encode (imp (termGraph v (addZero u) p b).encode
        (imp (termGraph v (addZero u) q b).encode (equivAt b p q).encode))) := by
  intro b p q hvs hg hds hp hq
  have hv : ∀ a ∈ u.varFinset, v a < b := by
    intro a ha; apply hvs a; simpa [addZero, binaryTerm, Term.varFinset] using ha
  have hd : ∀ a ∈ u.varFinset, KDerivation (imp g.encode (domainAt b (v a)).encode) := by
    intro a ha; apply hds a; simpa [addZero, binaryTerm, Term.varFinset] using ha
  let c := b+1
  let d := c+64
  let s := addZero u
  have hgb : b ∉ g.free := by intro hh; have := hg b hh; omega
  have hgc : c ∉ g.free := by intro hh; have := hg c hh; dsimp [c] at *; omega
  have hfirst := (termGraph_base_transport v u (b+64) d b (by omega)
    (by dsimp [d,c]; omega) (by intro a ha; have := hv a ha; omega)
    (by intro a ha; have := hv a ha; dsimp [d,c]; omega)).1
  have hvd : ∀ a ∈ u.varFinset, v a < d := by
    intro a ha; have := hv a ha; dsimp [d,c]; omega
  have hgd : ∀ x ∈ g.free, x < d := by
    intro x hx; have := hg x hx; dsimp [d,c]; omega
  have hdd : ∀ a ∈ u.varFinset, KDerivation (imp g.encode (domainAt d (v a)).encode) := by
    intro a ha
    exact compose (hd a ha)
      (domainAt_transport b d (v a) (by have := hv a ha; omega) (by have := hvd a ha; omega))
  have hfun := ih d b c hvd hgd hdd (by dsimp [d,c]; omega) (by dsimp [d]; omega)
  have heq := (equivAt_base_alpha d (c+1) b c
    (by dsimp [d,c]; omega) (by dsimp [d,c]; omega)
    (by dsimp [c]; omega) (by omega)).forward
  have hchild : KDerivation (imp g.encode (imp (termGraph v u b (b+64)).encode
      (imp (termGraph v u c (c+64)).encode (equivAt (c+1) b c).encode))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let A := (termGraph v u b (b+64)).encode
    let B := (termGraph v u c d).encode
    let Γ := [B,A,g.encode]
    have hg' : Context Γ g.encode := .hypothesis (by simp [Γ])
    have hA : Context Γ A := .hypothesis (by simp [Γ])
    have hB : Context Γ B := .head _ _
    exact .mp (.mp hB (.mp (.mp hA (.closed hfirst)) (.mp hg' (.closed hfun)))) (.closed heq)
  have h := functionality_of_child v u b c p q g (by dsimp [c]; omega) hp hq hv hgb hgc hchild
  have htransport := (termGraph_base_transport v s b c q hq (by dsimp [c]; omega)
    hvs (by intro a ha; have := hvs a ha; dsimp [c]; omega)).1
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(termGraph v s q b).encode, (termGraph v s p b).encode, g.encode]
  have hg' : Context Γ g.encode := .hypothesis (by simp [Γ])
  have hp' : Context Γ (termGraph v s p b).encode := .hypothesis (by simp [Γ])
  have hq' : Context Γ (termGraph v s q b).encode := .head _ _
  exact .mp (.mp hq' (.closed htransport)) (.mp hp' (.mp hg' (.closed h)))

/-- All terms in the right-zero closure have guarded graph functionality. -/
noncomputable def functional {α : Type} [DecidableEq α] (v : α → Nat)
    (g : Formula) {t : Peano.language.Term α} (ht : RightZeroTerm t) :
    ∀ b p q, (∀ a ∈ t.varFinset, v a < b) → (∀ x ∈ g.free, x < b) →
      (∀ a ∈ t.varFinset, KDerivation (imp g.encode (domainAt b (v a)).encode)) →
      p < b → q < b → KDerivation (imp g.encode (imp (termGraph v t p b).encode
        (imp (termGraph v t q b).encode (equivAt b p q).encode))) := by
  induction ht with
  | unary h => exact unary_functional v g h
  | @addZero u h ih =>
      exact add_zero_step v g u ih

end PASoundness.PAtoCompactRightZeroTermFunctional

#print axioms PASoundness.PAtoCompactRightZeroTermFunctional.add_zero_step
#print axioms PASoundness.PAtoCompactRightZeroTermFunctional.functional
