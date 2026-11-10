import PASoundness.PAtoCompactFirstFactorDiamondPoint
import PASoundness.PAtoCompactPAAddSuccDiamondExistenceLogic
import PASoundness.PAtoCompactPAAddSuccDiamondExistenceVacuity
import PASoundness.PAtoCompactSuccTermTotality
import PASoundness.PAtoCompactAllTermsTotalityClosed
import PASoundness.PAtoCompactMultiplicationCandidateTotalityClosed
import PASoundness.PAtoCompactMultiplicationArbitraryFromFixed
import PASoundness.PAtoCompactGuardedVacuity

/-! Reduce the guarded first-factor multiplication diamond to an explicit
same-witness successor/product/sum proof. Child term-graph existence and old
product existence are constructed; the remaining relational proof is not. -/
namespace PASoundness.PAtoCompactFirstFactorDiamondReduction

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactSuccTermTotality
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactGuardedVacuity
open PASoundness.PAtoCompactFirstFactorDiamondBody PASoundness.PAtoCompactFirstFactorDiamondPoint
open PASoundness.PAtoCompactFirstFactorDiamondVacuity
open PASoundness.PAtoCompactPAAddSuccDiamondExistenceVacuity
open PASoundness.PAtoCompactPAAddSuccDiamondExistenceLogic
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactFreeVacuity

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Given both child graphs and their old candidate product, this explicit K
proof input constructs a successor and a common output satisfying both sum and
new-product relations. It is not asserted to be inhabited here. -/
abbrev RemainingRelation (t u : Peano.Term) : Type :=
  let A := (Peano.mul (Peano.succ t) u).equal (Peano.add (Peano.mul t u) u)
  let q := guardBase A
  let e := q+100
  let x := q+1
  let y := q+2
  let p := q+3
  let sx := q+4
  KDerivation (imp (termGraph id t x e).encode
    (imp (termGraph id u y e).encode
      (imp (andF (domainAt e p) (mulAt e x y p)).encode
        (existsCode sx (existsCode q (tailBody e x y p sx q).encode)))))

/-- Assemble the guarded diamond using all-term graph totality, candidate
product totality, and the explicit remaining same-witness relation proof. -/
noncomputable def package_from_relation (t u : Peano.Term) (relation : RemainingRelation t u) :
    let A := (Peano.mul (Peano.succ t) u).equal (Peano.add (Peano.mul t u) u)
    let q := guardBase A
    KDerivation (imp (guardFormula A).encode
      (existsCode (q+1) (existsCode (q+2) (existsCode (q+3)
        (existsCode (q+4) (existsCode q (diamond t u q))))))) := by
  let A := (Peano.mul (Peano.succ t) u).equal (Peano.add (Peano.mul t u) u)
  let q := guardBase A
  let e := q+100
  let x := q+1
  let y := q+2
  let p := q+3
  let sx := q+4
  let g := guardFormula A
  let T := (termGraph id t x e).encode
  let U := (termGraph id u y e).encode
  let V := (andF (domainAt e p) (mulAt e x y p)).encode
  let B := (tailBody e x y p sx q).encode
  let R := (PAtoCompactFirstFactorDiamondVacuity.closedDiamondF t u q).encode
  have hf : ∀ a ∈ A.freeVarFinset, a < q := by
    intro a ha
    have hh : a ≤ A.freeVarFinset.sup id := Finset.le_sup (f := id) ha
    dsimp [q, guardBase]
    omega
  have ht : ∀ a ∈ t.varFinset, a < q := by
    intro a ha
    apply hf
    simp [A, Peano.mul, Peano.add, Peano.succ, eq_free, Term.varFinset, ha]
  have hu : ∀ a ∈ u.varFinset, a < q := by
    intro a ha
    apply hf
    simp [A, Peano.mul, Peano.add, Peano.succ, eq_free, Term.varFinset, ha]
  have hg : ∀ a ∈ g.free, a < q := by
    intro a ha
    exact hf a (guardFormula_free_subset A ha)
  have hcoverT : ∀ a ∈ t.varFinset, id a ∈ A.freeVarFinset := by
    intro a ha
    simp [A, Peano.mul, Peano.add, Peano.succ, eq_free, Term.varFinset, ha]
  have hcoverU : ∀ a ∈ u.varFinset, id a ∈ A.freeVarFinset := by
    intro a ha
    simp [A, Peano.mul, Peano.add, Peano.succ, eq_free, Term.varFinset, ha]
  have hT : KDerivation (imp g.encode (existsCode x T)) := by
    apply PAtoCompactAllTermsTotalityClosed.guarded_total id A t e x
    · dsimp [e,x]; omega
    · intro a ha; have := hf a ha; dsimp [x]; omega
    · exact hcoverT
  have hU : KDerivation (imp g.encode (existsCode y U)) := by
    apply PAtoCompactAllTermsTotalityClosed.guarded_total id A u e y
    · dsimp [e,y]; omega
    · intro a ha; have := hf a ha; dsimp [y]; omega
    · exact hcoverU
  have hP : KDerivation (imp T (imp U (existsCode p V))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [U,T]
    have hU' : Context Γ U := .head _ _
    have hT' : Context Γ T := .hypothesis (by simp [Γ])
    have hdx : Context Γ (domainAt e x).encode := .mp hT' (.closed (termGraph_domain id t x e))
    have hdy : Context Γ (domainAt e y).encode := .mp hU' (.closed (termGraph_domain id u y e))
    have hmul := PAtoCompactMultiplicationArbitraryFromFixed.arbitrary_from_fixed
      PAtoCompactMultiplicationCandidateTotalityClosed.candidate_total e x y p
      (by dsimp [e,x]; omega) (by dsimp [e,y]; omega) (by dsimp [e,p]; omega)
      (by dsimp [x,p]; omega) (by dsimp [y,p]; omega)
    exact .mp hdy (.mp hdx (.closed hmul))
  have hrel : KDerivation (imp T (imp U (imp V (existsCode sx (existsCode q B))))) := by
    simpa [RemainingRelation, A, q, e, x, y, p, sx, T, U, V, B] using relation
  have vg : ∀ k, k ∈ [x,y,p,sx,q] → KDerivation (imp g.encode (allCode k g.encode)) := by
    intro k hk
    have hkq : q ≤ k := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; dsimp [x,y,p,sx] at hk; omega
    exact guard_vacuity g q k hg hkq
  have vT : ∀ k, k ∈ [y,p,sx,q] → KDerivation (imp T (allCode k T)) := by
    intro k hk
    have hkq : q ≤ k := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; dsimp [y,p,sx] at hk; omega
    have hko : k ≠ x := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; dsimp [x,y,p,sx] at hk; omega
    exact graph_vacuity t q e x k ht hkq hko
  have vU : ∀ k, k ∈ [p,sx,q] → KDerivation (imp U (allCode k U)) := by
    intro k hk
    have hkq : q ≤ k := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; dsimp [p,sx] at hk; omega
    have hko : k ≠ y := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; dsimp [y,p,sx] at hk; omega
    exact graph_vacuity u q e y k hu hkq hko
  have vV : ∀ k, k ∈ [sx,q] → KDerivation (imp V (allCode k V)) := by
    intro k hk
    have hkx : k ≠ x := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; dsimp [x,sx] at hk; omega
    have hky : k ≠ y := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; dsimp [y,sx] at hk; omega
    have hkp : k ≠ p := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; dsimp [p,sx] at hk; omega
    apply free_vacuity
    intro h
    simp only [andF_free, Finset.mem_union] at h
    rcases h with h | h
    · have hh := domainAt_free e p h; exact hkp (Finset.mem_singleton.mp hh)
    · have hh := mulAt_free e x y p h; simp [hkx,hky,hkp] at hh
  have vR : ∀ k, k ∈ [x,y,p,sx,q] → KDerivation (imp R (allCode k R)) := by
    intro k hk
    apply PAtoCompactFirstFactorDiamondVacuity.closedDiamond_vacuity t u q k
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    dsimp [x,y,p,sx] at hk
    omega
  have h := five_witness_compose x y p sx q g.encode T U V B R hT hU hP hrel
    (point t u q) vg vT vU vV vR
  simpa [A, q, e, x, y, p, sx, g, T, U, V, B, R, PAtoCompactFirstFactorDiamondVacuity.closedDiamond_encode] using h

/-- The guarded first-factor formula follows from the displayed remaining
same-witness relation proof, without assuming PA or K soundness. -/
noncomputable def guarded_from_relation (t u : Peano.Term) (relation : RemainingRelation t u) :
    KDerivation (guardedCode ((Peano.mul (Peano.succ t) u).equal (Peano.add (Peano.mul t u) u))) :=
  guarded_first_successor_of_diamond t u (package_from_relation t u relation)

end PASoundness.PAtoCompactFirstFactorDiamondReduction

#print axioms PASoundness.PAtoCompactFirstFactorDiamondReduction.RemainingRelation
#print axioms PASoundness.PAtoCompactFirstFactorDiamondReduction.package_from_relation
#print axioms PASoundness.PAtoCompactFirstFactorDiamondReduction.guarded_from_relation
