import PASoundness.PAtoCompactPAAddSuccDiamondExistencePoint
import PASoundness.PAtoCompactPAAddSuccDiamondExistenceLogic
import PASoundness.PAtoCompactAdditionArbitraryTotality
import PASoundness.PAtoCompactTermGraphBinderRange

/-! Guarded existence of an addition-successor diamond from explicit child
term-graph existence proofs. This finite-K constructor does not assume graph
functionality or invoke PA/K semantic soundness. -/
namespace PASoundness.PAtoCompactPAAddSuccDiamondExistence
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactSuccTermTotality PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactFreeNames
open PASoundness.PAtoCompactPAAddSuccDiamondExistenceVacuity
open PASoundness.PAtoCompactPAAddSuccDiamondExistencePoint
open PASoundness.PAtoCompactPAAddSuccDiamondExistenceLogic
open PASoundness.PAtoCompactPAAddSuccDynamicWitness
open PASoundness.PAtoCompactAdditionArbitraryTotality
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] PASoundness.CompactProof.imp Cantor.pair Cantor.triangle

/-- Construct the shared arithmetic diamond from two explicitly supplied
child-existence derivations. Source and guard names must lie below q; the
canonical internal labels q+1,...,q+4 are fresh syntactic binders. -/
noncomputable def diamond_of_children (t u : Peano.Term) (g : Formula) (q : Nat)
    (ht : ∀ a ∈ t.varFinset, a < q) (hu : ∀ a ∈ u.varFinset, a < q)
    (hg : ∀ a ∈ g.free, a < q)
    (childT : KDerivation (imp g.encode
      (existsCode (q+1) (termGraph id t (q+1) (q+100)).encode)))
    (childU : KDerivation (imp g.encode
      (existsCode (q+2) (termGraph id u (q+2) (q+100)).encode))) :
    KDerivation (imp g.encode (closedDiamondF t u q).encode) := by
  let x := q+1
  let y := q+2
  let z := q+3
  let m := q+4
  let e := q+100
  let T := (termGraph id t x e).encode
  let U := (termGraph id u y e).encode
  let V := (andF (domainAt e z) (addAt e x y z)).encode
  let B := (body e x y z m q).encode
  let R := (closedDiamondF t u q).encode
  have hz : KDerivation (imp T (imp U (existsCode z V))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [U,T]
    have hU : Context Γ U := .head _ _
    have hT : Context Γ T := .hypothesis (by simp [Γ])
    have hdX : Context Γ (domainAt e x).encode := .mp hT (.closed (termGraph_domain id t x e))
    have hdY : Context Γ (domainAt e y).encode := .mp hU (.closed (termGraph_domain id u y e))
    have ha := addition_total e x y z (by dsimp [e,x]; omega) (by dsimp [e,y]; omega)
      (by dsimp [e,z]; omega) (by dsimp [x,z]; omega) (by dsimp [y,z]; omega)
    exact .mp hdY (.mp hdX (.closed ha))
  have hmn : KDerivation (imp T (imp U (imp V (existsCode m (existsCode q B))))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Γ := [V,U,T]
    have hV : Context Γ V := .head _ _
    have hU : Context Γ U := .hypothesis (by simp [Γ])
    have hdY : Context Γ (domainAt e y).encode := .mp hU (.closed (termGraph_domain id u y e))
    have hdZ : Context Γ (domainAt e z).encode := Context.conjunctionLeft hV
    have ha : Context Γ (addAt e x y z).encode := Context.conjunctionRight hV
    have hs := dynamic_exists e x y z m q (by dsimp [e]; omega)
      (by dsimp [e,x]; omega) (by dsimp [e,y]; omega) (by dsimp [e,z]; omega)
      (by dsimp [e,m]; omega) (by dsimp [e]; omega)
      (by dsimp [m,x]; omega) (by dsimp [m,y]; omega) (by dsimp [m,z]; omega)
      (by dsimp [x]; omega) (by dsimp [y]; omega) (by dsimp [z]; omega) (by dsimp [m]; omega)
    have hr := Context.mp ha (Context.mp hdZ (Context.mp hdY (.closed hs)))
    simpa [result, Formula.encode, existsCode, B] using hr
  have vg : ∀ k, k ∈ [x,y,z,m,q] → KDerivation (imp g.encode (allCode k g.encode)) := by
    intro k hk
    have hkq : q ≤ k := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; dsimp [x,y,z,m] at hk; omega
    exact guard_vacuity g q k hg hkq
  have vT : ∀ k, k ∈ [y,z,m,q] → KDerivation (imp T (allCode k T)) := by
    intro k hk
    have hkq : q ≤ k := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; dsimp [y,z,m] at hk; omega
    have hko : k ≠ x := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; dsimp [x,y,z,m] at hk; omega
    exact graph_vacuity t q e x k ht hkq hko
  have vU : ∀ k, k ∈ [z,m,q] → KDerivation (imp U (allCode k U)) := by
    intro k hk
    have hkq : q ≤ k := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; dsimp [z,m] at hk; omega
    have hko : k ≠ y := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; dsimp [y,z,m] at hk; omega
    exact graph_vacuity u q e y k hu hkq hko
  have vV : ∀ k, k ∈ [m,q] → KDerivation (imp V (allCode k V)) := by
    intro k hk
    have hkx : k ≠ x := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; dsimp [x,m] at hk; omega
    have hky : k ≠ y := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; dsimp [y,m] at hk; omega
    have hkz : k ≠ z := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; dsimp [z,m] at hk; omega
    apply free_vacuity
    intro h
    simp only [andF_free, Finset.mem_union] at h
    rcases h with h | h
    · have hh := domainAt_free e z h; exact hkz (Finset.mem_singleton.mp hh)
    · have hh := addAt_free e x y z h; simp [hkx,hky,hkz] at hh
  have vR : ∀ k, k ∈ [x,y,z,m,q] → KDerivation (imp R (allCode k R)) := by
    intro k hk
    apply closedDiamond_vacuity t u q k
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    dsimp [x,y,z,m] at hk
    omega
  exact five_witness_compose x y z m q g.encode T U V B R childT childU hz hmn
    (point t u q) vg vT vU vV vR

end PASoundness.PAtoCompactPAAddSuccDiamondExistence
#print axioms PASoundness.PAtoCompactPAAddSuccDiamondExistence.diamond_of_children
