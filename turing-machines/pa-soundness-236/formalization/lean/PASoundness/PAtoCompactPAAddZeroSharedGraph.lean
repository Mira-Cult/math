import PASoundness.PAtoCompactTermZeroGuarded
import PASoundness.PAtoCompactAddTermBody
import PASoundness.PAtoCompactVariableTermTotality

/-! Finite K introduction of an addition-by-zero term graph from a shared
child/output witness. Candidate, zero and addition relation remain inputs. -/
namespace PASoundness.PAtoCompactPAAddZeroSharedGraph
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermZeroGuarded
open PASoundness.PAtoCompactAddTermBody PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactVariableTermTotality PASoundness.PAtoCompactTermGraphReplace
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactScopedAlphaInvariant
set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem replace_outer_body {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) (b q : Nat) (hq : q < b)
    (hv : ∀ a ∈ t.varFinset, v a < b) :
    replace b q (rebasedBody v t (.func .zero Fin.elim0) b (b+1) b q) =
      rebasedBody v t (.func .zero Fin.elim0) q (b+1) b q := by
  rw [replace_rebasedBody v t (.func .zero Fin.elim0) b (b+1) b q b q (by omega)]
  have hm : ∀ a ∈ t.varFinset, (rename b q ∘ v) a = v a := by
    intro a ha
    simp [Function.comp_apply, rename, show v a ≠ b by have := hv a ha; omega]
  have hz : ∀ a ∈ (.func .zero Fin.elim0 : Peano.language.Term α).varFinset,
      (rename b q ∘ v) a = v a := by simp [Term.varFinset]
  unfold rebasedBody
  rw [termGraph_name_agree t _ v hm, termGraph_name_agree _ _ v hz]
  simp [rename, show q ≠ b by omega]

def shared_graph_intro {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) (b q : Nat) (hq : q < b)
    (hv : ∀ a ∈ t.varFinset, v a < b) :
    KDerivation (imp (domainAt b q).encode
      (imp (termGraph v t q (b+64)).encode
        (imp (termGraph v (.func .zero Fin.elim0) (b+1) (b+64+termCost t)).encode
          (imp (addAt b q (b+1) q).encode
            (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) q b).encode)))) := by
  let z : Peano.language.Term α := .func .zero Fin.elim0
  let N := rebasedBody v t z b (b+1) b q
  let M := rebasedBody v t z q (b+1) b q
  have hbn : b ∉ N.binders := body_below_not_binder v t z b (b+1) b q b (by omega)
  have hqn : q ∉ N.binders := body_below_not_binder v t z b (b+1) b q q (by omega)
  have h1n : b+1 ∉ M.binders := body_below_not_binder v t z q (b+1) b q (b+1) (by omega)
  have hi := existsIntroduce (b+1) M h1n
  have ho := exists_from_instance b q (.ex (b+1) N) (by omega)
    (by simpa [Formula.binders] using hbn)
    (by simpa [Formula.binders, show q ≠ b+1 by omega] using hqn)
  have hrep : replace b q (.ex (b+1) N) = .ex (b+1) M := by
    simp only [replace]
    exact congrArg (Formula.ex (b+1)) (replace_outer_body v t b q hq hv)
  rw [hrep] at ho
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(addAt b q (b+1) q).encode, (termGraph v z (b+1) (b+64+termCost t)).encode,
    (termGraph v t q (b+64)).encode, (domainAt b q).encode]
  have hr : Context Γ (addAt b q (b+1) q).encode := .hypothesis (by simp [Γ])
  have hz : Context Γ (termGraph v z (b+1) (b+64+termCost t)).encode := .hypothesis (by simp [Γ])
  have ht : Context Γ (termGraph v t q (b+64)).encode := .hypothesis (by simp [Γ])
  have hd : Context Γ (domainAt b q).encode := .hypothesis (by simp [Γ])
  have hm : Context Γ M.encode := by
    have h := Context.conjunctionIntro ht (Context.conjunctionIntro hz hr)
    simpa [M, rebasedBody, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using h
  have he : Context Γ (existsCode b (existsCode (b+1) N.encode)) := .mp (.mp hm (.closed hi)) (.closed ho)
  have h := Context.conjunctionIntro hd he
  change Context Γ (andF (domainAt b q) (.ex b (.ex (b+1) N))).encode
  simpa only [andF, CompactNamed.Formula.not, Formula.encode, both, neg, existsCode] using h
#print axioms shared_graph_intro
end PASoundness.PAtoCompactPAAddZeroSharedGraph
