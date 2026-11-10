import PASoundness.PAtoCompactAddTermBody
import PASoundness.PAtoCompactTermZeroGuarded

/-! Capture-safe introduction of an addition term graph using explicitly
named witnesses below its allocator. This supplies no arithmetic existence or
functionality. -/
namespace PASoundness.PAtoCompactPAAddSuccSharedSmallWitness

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactAddTermBody
open PASoundness.PAtoCompactTermGraphBinderRange PASoundness.PAtoCompactTermZeroGuarded
open PASoundness.PAtoCompactVariableTermTotality
open PASoundness.PAtoCompactScopedAlphaInvariant

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] PASoundness.CompactProof.imp Cantor.pair Cantor.triangle

/-- Introducing the generated addition graph from two possibly aliased
small witness labels. Source names, witnesses, and output stay below the
allocator, so no private binder captures them. -/
def add_graph_from_witnesses {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (b out x y : Nat)
    (hout : out < b) (hx : x < b) (hy : y < b)
    (ht : ∀ a ∈ t.varFinset, v a < b) (hu : ∀ a ∈ u.varFinset, v a < b) :
    KDerivation (imp (domainAt b out).encode
      (imp (termGraph v t x (b+64)).encode
        (imp (termGraph v u y (b+64+termCost t)).encode
          (imp (addAt b x y out).encode
            (termGraph v (binaryTerm true t u) out b).encode)))) := by
  let N := rebasedBody v t u b (b+1) b out
  have hbn : b ∉ N.binders := body_below_not_binder v t u b (b+1) b out b (by omega)
  have hb1n : b+1 ∉ N.binders := body_below_not_binder v t u b (b+1) b out (b+1) (by omega)
  have hxn : x ∉ N.binders := body_below_not_binder v t u b (b+1) b out x (by omega)
  have hyn : y ∉ N.binders := body_below_not_binder v t u b (b+1) b out y (by omega)
  have hfirst : replace b x N = rebasedBody v t u x (b+1) b out := by
    dsimp [N]
    rw [replace_rebasedBody v t u b (b+1) b out b x (by omega)]
    have htv : ∀ a ∈ t.varFinset, (rename b x ∘ v) a = v a := by
      intro a ha
      simp [Function.comp_apply, rename, show v a ≠ b by have := ht a ha; omega]
    have huv : ∀ a ∈ u.varFinset, (rename b x ∘ v) a = v a := by
      intro a ha
      simp [Function.comp_apply, rename, show v a ≠ b by have := hu a ha; omega]
    unfold rebasedBody
    rw [termGraph_name_agree t _ v htv, termGraph_name_agree u _ v huv]
    simp [rename, show out ≠ b by omega]
  have hsecond : replace (b+1) y (replace b x N) = rebasedBody v t u x y b out := by
    rw [hfirst, replace_rebasedBody v t u x (b+1) b out (b+1) y (by omega)]
    have htv : ∀ a ∈ t.varFinset, (rename (b+1) y ∘ v) a = v a := by
      intro a ha
      simp [Function.comp_apply, rename, show v a ≠ b+1 by have := ht a ha; omega]
    have huv : ∀ a ∈ u.varFinset, (rename (b+1) y ∘ v) a = v a := by
      intro a ha
      simp [Function.comp_apply, rename, show v a ≠ b+1 by have := hu a ha; omega]
    unfold rebasedBody
    rw [termGraph_name_agree t _ v htv, termGraph_name_agree u _ v huv]
    simp [rename, show out ≠ b+1 by omega, show x ≠ b+1 by omega]
  have hi := exists_from_instance (b+1) y (replace b x N) (by omega)
    (by simpa only [replace_binders] using hb1n)
    (by simpa only [replace_binders] using hyn)
  rw [hsecond] at hi
  have ho := exists_from_instance b x (.ex (b+1) N) (by omega)
    (by simpa [Formula.binders, show b ≠ b+1 by omega] using hbn)
    (by simpa [Formula.binders, show x ≠ b+1 by omega] using hxn)
  change KDerivation (imp (existsCode (b+1) (replace b x N).encode)
    (existsCode b (Formula.ex (b+1) N).encode)) at ho
  have he := compose hi ho
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(addAt b x y out).encode, (termGraph v u y (b+64+termCost t)).encode,
    (termGraph v t x (b+64)).encode, (domainAt b out).encode]
  have hR : Context Γ (addAt b x y out).encode := .head _ _
  have hU : Context Γ (termGraph v u y (b+64+termCost t)).encode := .hypothesis (by simp [Γ])
  have hT : Context Γ (termGraph v t x (b+64)).encode := .hypothesis (by simp [Γ])
  have hD : Context Γ (domainAt b out).encode := .hypothesis (by simp [Γ])
  have hbody : Context Γ (rebasedBody v t u x y b out).encode := by
    have h := Context.conjunctionIntro hT (Context.conjunctionIntro hU hR)
    simpa [rebasedBody, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using h
  have hex := Context.mp hbody (.closed he)
  have hh := Context.conjunctionIntro hD hex
  simpa [N, rebasedBody, binaryTerm, termGraph, andF, CompactNamed.Formula.not,
    Formula.encode, both, neg, existsCode] using hh

theorem add_graph_from_witnesses_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (b out x y : Nat)
    (hout : out < b) (hx : x < b) (hy : y < b)
    (ht : ∀ a ∈ t.varFinset, v a < b) (hu : ∀ a ∈ u.varFinset, v a < b) :
    theoremCode (certificate (add_graph_from_witnesses v t u b out x y hout hx hy ht hu)) =
      imp (domainAt b out).encode (imp (termGraph v t x (b+64)).encode
        (imp (termGraph v u y (b+64+termCost t)).encode (imp (addAt b x y out).encode
          (termGraph v (binaryTerm true t u) out b).encode))) := certificate_correct _

end PASoundness.PAtoCompactPAAddSuccSharedSmallWitness

#print axioms PASoundness.PAtoCompactPAAddSuccSharedSmallWitness.add_graph_from_witnesses
#print axioms PASoundness.PAtoCompactPAAddSuccSharedSmallWitness.add_graph_from_witnesses_certificate
