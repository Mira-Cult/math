import PASoundness.PAtoCompactFirstFactorDiamondReduction
import PASoundness.PAtoCompactRawAndQuotientSuccessorWitness

/-! A fresh candidate successor is constructed from the first child graph.
A continuation producing the shared sum/product output remains explicit. -/
namespace PASoundness.PAtoCompactFirstFactorSuccessorReduction

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactSuccTermTotality
open PASoundness.PAtoCompactFirstFactorDiamondReduction PASoundness.PAtoCompactFirstFactorDiamondPoint
open PASoundness.PAtoCompactPAAddSuccDiamondExistenceVacuity
open PASoundness.PAtoCompactPAAddSuccDiamondExistenceLogic
open PASoundness.PAtoCompactRawAndQuotientSuccessorWitness
open PASoundness.PAtoCompactQuotientSuccessorTotality
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactTermGraphBinderRange

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A supplied finite K proof extends the chosen candidate raw successor to a
shared output satisfying the sum and new-product relations. -/
abbrev RemainingContinuation (t u : Peano.Term) : Type :=
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
        (imp (rawAt e x sx).encode (imp (domainAt e sx).encode
          (imp (succAt e x sx).encode (existsCode q (tailBody e x y p sx q).encode)))))))

/-- Construct the successor from the first child graph, and apply the
continuation to that same witness. The continuation remains explicit. -/
noncomputable def relation_from_continuation (t u : Peano.Term)
    (continuation : RemainingContinuation t u) : RemainingRelation t u := by
  let A := (Peano.mul (Peano.succ t) u).equal (Peano.add (Peano.mul t u) u)
  let q := guardBase A
  let e := q+100
  let x := q+1
  let y := q+2
  let p := q+3
  let sx := q+4
  let T := (termGraph id t x e).encode
  let U := (termGraph id u y e).encode
  let V := (andF (domainAt e p) (mulAt e x y p)).encode
  let W := PAtoCompactRawAndQuotientSuccessorWitness.body e x sx
  let F := tailBody e x y p sx q
  let E := Formula.ex sx (Formula.ex q F)
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
  have vT : KDerivation (imp T (allCode sx T)) :=
    graph_vacuity t q e x sx ht (by dsimp [sx]; omega) (by dsimp [sx,x]; omega)
  have vU : KDerivation (imp U (allCode sx U)) :=
    graph_vacuity u q e y sx hu (by dsimp [sx]; omega) (by dsimp [sx,y]; omega)
  have vV : KDerivation (imp V (allCode sx V)) := by
    apply free_vacuity
    intro h
    simp only [andF_free, Finset.mem_union] at h
    rcases h with h | h
    · have hh := domainAt_free e p h
      have he := Finset.mem_singleton.mp hh
      dsimp [sx,p] at he
      omega
    · have hh := mulAt_free e x y p h
      simp [show sx ≠ x by dsimp [sx,x]; omega,
        show sx ≠ y by dsimp [sx,y]; omega,
        show sx ≠ p by dsimp [sx,p]; omega] at hh
  have vE : KDerivation (imp E.encode (allCode sx E.encode)) := by
    apply free_vacuity
    simp [E, Formula.free]
  have hbody : sx ∉ F.binders := by
    intro h
    simp only [F, tailBody, andF_binders, Finset.mem_union] at h
    rcases h with h | h | h | h | h
    · have hh := domainAt_private e sx sx h; dsimp [e,sx] at hh; omega
    · have hh := domainAt_private e q sx h; dsimp [e,sx] at hh; omega
    · have hh := succAt_private e x sx sx h; dsimp [e,sx] at hh; omega
    · have hh := addAt_private e p y q sx h; dsimp [e,sx] at hh; omega
    · have hh := mulAt_private e sx y q sx h; dsimp [e,sx] at hh; omega
  have hEF : sx ∉ (Formula.ex q F).binders := by
    simp only [Formula.binders, Finset.mem_insert, not_or]
    exact ⟨by dsimp [sx]; omega, hbody⟩
  have hcont : KDerivation (imp T (imp U (imp V
      (imp (rawAt e x sx).encode (imp (domainAt e sx).encode
        (imp (succAt e x sx).encode (existsCode q F.encode))))))) := by
    simpa [RemainingContinuation, A,q,e,x,y,p,sx,T,U,V,F] using continuation
  have hsucc := successor_exists e x sx (by dsimp [e,x]; omega)
    (by dsimp [e,sx]; omega) (by dsimp [sx,x]; omega)
  change KDerivation (imp T (imp U (imp V (existsCode sx (existsCode q F.encode)))))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [V,U,T]
  have hT : Context Γ T := .hypothesis (by simp [Γ])
  have hdx : Context Γ (domainAt e x).encode := .mp hT (.closed (termGraph_domain id t x e))
  have hs : Context Γ (existsCode sx W.encode) := .mp hdx (.closed hsucc)
  have hctx : ∀ h, h ∈ Γ → KDerivation (imp h (allCode sx h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases hv : h = V
    · subst h; exact vV
    by_cases hu : h = U
    · subst h; exact vU
    have ht : h = T := by simpa [hv, hu] using hh
    subst h
    exact vT
  have hpoint : Context Γ (imp W.encode E.encode) := by
    apply Context.deduction
    let Δ := [W.encode,V,U,T]
    have hW : Context Δ W.encode := .head _ _
    have hboth : Context Δ (both (rawAt e x sx).encode
        (both (domainAt e sx).encode (succAt e x sx).encode)) := by
      simpa [W, PAtoCompactRawAndQuotientSuccessorWitness.body, andF,
        CompactNamed.Formula.not, Formula.encode, both, neg] using hW
    have hraw := Context.conjunctionLeft hboth
    have hrest := Context.conjunctionRight hboth
    have hds := Context.conjunctionLeft hrest
    have hsq := Context.conjunctionRight hrest
    have hV : Context Δ V := .hypothesis (by simp [Δ])
    have hU : Context Δ U := .hypothesis (by simp [Δ])
    have hT' : Context Δ T := .hypothesis (by simp [Δ])
    have hq : Context Δ (existsCode q F.encode) :=
      .mp hsq (.mp hds (.mp hraw (.mp hV (.mp hU (.mp hT' (.closed hcont))))))
    have hi := existsIntroduce sx (Formula.ex q F) hEF
    have hr := Context.mp (by simpa [Formula.encode, existsCode] using hq) (.closed hi)
    simpa [E, Formula.encode, existsCode] using hr
  have hresult := contextual_exists_elim sx W.encode E.encode hctx vE hpoint hs
  simpa [E, Formula.encode, existsCode] using hresult

/-- The guarded first-factor formula follows from the explicit continuation. -/
noncomputable def guarded_from_continuation (t u : Peano.Term)
    (continuation : RemainingContinuation t u) :
    KDerivation (guardedCode ((Peano.mul (Peano.succ t) u).equal (Peano.add (Peano.mul t u) u))) :=
  guarded_from_relation t u (relation_from_continuation t u continuation)

end PASoundness.PAtoCompactFirstFactorSuccessorReduction

#print axioms PASoundness.PAtoCompactFirstFactorSuccessorReduction.RemainingContinuation
#print axioms PASoundness.PAtoCompactFirstFactorSuccessorReduction.relation_from_continuation
#print axioms PASoundness.PAtoCompactFirstFactorSuccessorReduction.guarded_from_continuation
