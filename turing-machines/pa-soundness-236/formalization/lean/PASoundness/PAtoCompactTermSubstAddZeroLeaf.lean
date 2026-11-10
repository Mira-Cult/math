import PASoundness.PAtoCompactAddZeroUnaryFunctional
import PASoundness.PAtoCompactAddZeroGraphOutput
import PASoundness.PAtoCompactUnaryGraphFunctionalityFull
import PASoundness.PAtoCompactSuccTermTotality

/-! The selected-variable substitution leaf for a unary term plus zero.
The retained guard and graph are explicit, as are all candidate proofs. -/
namespace PASoundness.PAtoCompactTermSubstAddZeroLeaf
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactUnaryTermTransport
open PASoundness.PAtoCompactTermZeroGuarded PASoundness.PAtoCompactAddZeroGraphOutput
open PASoundness.PAtoCompactAllTermTransport PASoundness.PAtoCompactEquivMultiAlpha
open PASoundness.PAtoCompactAddZeroGraphFunctionalClosed
open PASoundness.PAtoCompactUnaryGraphFunctionalityFull PASoundness.PAtoCompactSuccTermTotality
open PASoundness.PAtoCompactGuardBaseTransport
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] PASoundness.CompactProof.imp Cantor.pair Cantor.triangle

def addZero {α : Type} (u : Peano.language.Term α) : Peano.language.Term α :=
  binaryTerm true u (.func .zero Fin.elim0)

/-- Unary-child right-zero graph functionality under an arbitrary guard
that supplies each used source variable's candidate condition. -/
noncomputable def add_zero_functional {α : Type} [DecidableEq α] (v : α → Nat)
    (g : Formula) (u : Peano.language.Term α) (hu : UnaryTerm u)
    (b p q : Nat) (hp : p < b) (hq : q < b)
    (hv : ∀ a ∈ u.varFinset, v a < b) (hg : ∀ x ∈ g.free, x < b)
    (hd : ∀ a ∈ u.varFinset, KDerivation (imp g.encode (domainAt b (v a)).encode)) :
    KDerivation (imp g.encode (imp (termGraph v (addZero u) p b).encode
      (imp (termGraph v (addZero u) q b).encode (equivAt b p q).encode))) := by
  let c := b+1
  let d := c+64
  let s := addZero u
  have hvs : ∀ a ∈ s.varFinset, v a < b := by
    intro a ha
    have ha' : a ∈ u.varFinset := by simpa [s, addZero, binaryTerm, Term.varFinset] using ha
    exact hv a ha'
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
  have hfun := unary_functional v g hu d b c hvd hgd hdd
    (by dsimp [d,c]; omega) (by dsimp [d]; omega)
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

/-- Forward selected-variable graph alignment under the retained graph. -/
noncomputable def add_zero_leaf_forward {α : Type} [DecidableEq α] (v : α → Nat)
    (u : Peano.language.Term α) (b q r : Nat)
    (hq : q < b) (hr : r < b) (hv : ∀ a ∈ u.varFinset, v a < b) :
    KDerivation (imp (termGraph v (addZero u) q b).encode
      (imp (termGraph id (.var q : Peano.Term) r b).encode
        (termGraph v (addZero u) r b).encode)) := by
  have hvs : ∀ a ∈ (addZero u).varFinset, v a < b := by
    intro a ha; apply hv a; simpa [addZero, binaryTerm, Term.varFinset] using ha
  have ho := add_zero_output v u b q r hq hr hvs
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let G := (termGraph v (addZero u) q b).encode
  let V := (termGraph id (.var q : Peano.Term) r b).encode
  let Γ := [V,G]
  have hG : Context Γ G := .hypothesis (by simp [Γ])
  have hV : Context Γ V := Context.head _ _
  exact .mp (Context.conjunctionRight hV)
    (.mp hG (.mp (Context.conjunctionLeft hV) (.closed ho)))

/-- Reverse selected-variable graph alignment under the same retained graph. -/
noncomputable def add_zero_leaf_reverse {α : Type} [DecidableEq α] (v : α → Nat)
    (g : Formula) (u : Peano.language.Term α) (hu : UnaryTerm u)
    (b q r : Nat) (hq : q < b) (hr : r < b)
    (hv : ∀ a ∈ u.varFinset, v a < b) (hg : ∀ x ∈ g.free, x < b)
    (hd : ∀ a ∈ u.varFinset, KDerivation (imp g.encode (domainAt b (v a)).encode)) :
    KDerivation (imp g.encode (imp (termGraph v (addZero u) q b).encode
      (imp (termGraph v (addZero u) r b).encode
        (termGraph id (.var q : Peano.Term) r b).encode))) := by
  have hf := add_zero_functional v g u hu b q r hq hr hv hg hd
  have hdom := termGraph_domain v (addZero u) r b
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let G := (termGraph v (addZero u) q b).encode
  let T := (termGraph v (addZero u) r b).encode
  let Γ := [T,G,g.encode]
  have hg' : Context Γ g.encode := .hypothesis (by simp [Γ])
  have hG : Context Γ G := .hypothesis (by simp [Γ])
  have hT : Context Γ T := Context.head _ _
  have hD : Context Γ (domainAt b r).encode := .mp hT (.closed hdom)
  have hE : Context Γ (equivAt b q r).encode := .mp hT (.mp hG (.mp hg' (.closed hf)))
  exact Context.conjunctionIntro hD hE

end PASoundness.PAtoCompactTermSubstAddZeroLeaf

#print axioms PASoundness.PAtoCompactTermSubstAddZeroLeaf.add_zero_functional
#print axioms PASoundness.PAtoCompactTermSubstAddZeroLeaf.add_zero_leaf_forward
#print axioms PASoundness.PAtoCompactTermSubstAddZeroLeaf.add_zero_leaf_reverse
