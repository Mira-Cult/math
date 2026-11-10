import PASoundness.PAtoCompactFirstFactorSuccessorReduction
import PASoundness.PAtoCompactLiteralCutBaseSyntax

/-! A pointwise candidate literal-cut product extension supplies the remaining
first-factor continuation. The pointwise extension remains explicit proof data. -/
namespace PASoundness.PAtoCompactFirstFactorCutContinuation

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactSuccTermTotality
open PASoundness.PAtoCompactFirstFactorSuccessorReduction PASoundness.PAtoCompactFirstFactorDiamondPoint
open PASoundness.PAtoCompactPAAddSuccDiamondExistenceVacuity
open PASoundness.PAtoCompactPAAddSuccDiamondExistenceLogic
open PASoundness.PAtoCompactQuotientSuccessorTotality PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactLiteralCutBaseSyntax PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactFreeVacuity

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The single output simultaneously has the anchored cut, the actual sum,
and the extended product. -/
def cutOutput (e x y p sx q : Nat) : Formula :=
  andF (domainAt e q) (andF (literalCutAt e p y q)
    (andF (addAt e p y q) (mulAt e sx y q)))

/-- Explicit finite K extension input; it does not itself follow from the
conditional wrapper. The q label is existentially bound and syntactically
fresh for the other operands in the canonical allocation. -/
abbrev CutExtension (t u : Peano.Term) : Type :=
  let A := (Peano.mul (Peano.succ t) u).equal (Peano.add (Peano.mul t u) u)
  let q := guardBase A
  let e := q+100
  let x := q+1
  let y := q+2
  let p := q+3
  let sx := q+4
  KDerivation (imp (domainAt e x).encode (imp (domainAt e y).encode
    (imp (domainAt e p).encode (imp (rawAt e x sx).encode (imp (domainAt e sx).encode
      (imp (mulAt e x y p).encode (existsCode q (cutOutput e x y p sx q).encode)))))))

/-- Supply the displayed continuation from a candidate cut extension, reusing
one final output and the same already chosen successor. -/
noncomputable def continuation_from_cut (t u : Peano.Term)
    (extension : CutExtension t u) : RemainingContinuation t u := by
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
  let R := (rawAt e x sx).encode
  let D := (domainAt e sx).encode
  let S := (succAt e x sx).encode
  let W := cutOutput e x y p sx q
  let F := tailBody e x y p sx q
  let E := Formula.ex q F
  have hf : ∀ a ∈ A.freeVarFinset, a < q := by
    intro a ha
    have hh : a ≤ A.freeVarFinset.sup id := Finset.le_sup (f := id) ha
    dsimp [q, guardBase]
    omega
  have ht : ∀ a ∈ t.varFinset, a < q := by
    intro a ha; apply hf
    simp [A, Peano.mul, Peano.add, Peano.succ, eq_free, Term.varFinset, ha]
  have hu : ∀ a ∈ u.varFinset, a < q := by
    intro a ha; apply hf
    simp [A, Peano.mul, Peano.add, Peano.succ, eq_free, Term.varFinset, ha]
  have vT : KDerivation (imp T (allCode q T)) :=
    graph_vacuity t q e x q ht (by omega) (by dsimp [x]; omega)
  have vU : KDerivation (imp U (allCode q U)) :=
    graph_vacuity u q e y q hu (by omega) (by dsimp [y]; omega)
  have vV : KDerivation (imp V (allCode q V)) := by
    apply free_vacuity
    intro h
    simp only [andF_free, Finset.mem_union] at h
    rcases h with h | h
    · have hh := domainAt_free e p h
      have he := Finset.mem_singleton.mp hh
      dsimp [p] at he; omega
    · have hh := mulAt_free e x y p h
      simp [show q ≠ x by dsimp [x]; omega,
        show q ≠ y by dsimp [y]; omega, show q ≠ p by dsimp [p]; omega] at hh
  have vR : KDerivation (imp R (allCode q R)) := by
    apply free_vacuity
    simp [R, rawAt, Formula.free, namedSuccessorBody, namedBoth, namedEither,
      show q ≠ x by dsimp [x]; omega, show q ≠ sx by dsimp [sx]; omega]
  have vD : KDerivation (imp D (allCode q D)) :=
    domain_vacuity e sx q (by dsimp [sx]; omega)
  have vS : KDerivation (imp S (allCode q S)) := by
    apply free_vacuity
    intro h
    have hh := succAt_free e x sx h
    simp [show q ≠ x by dsimp [x]; omega, show q ≠ sx by dsimp [sx]; omega] at hh
  have vE : KDerivation (imp E.encode (allCode q E.encode)) := by
    apply free_vacuity
    simp [E, Formula.free]
  have hF : q ∉ F.binders := by
    intro h
    simp only [F, tailBody, andF_binders, Finset.mem_union] at h
    rcases h with h | h | h | h | h
    · have hh := domainAt_private e sx q h; dsimp [e] at hh; omega
    · have hh := domainAt_private e q q h; dsimp [e] at hh; omega
    · have hh := succAt_private e x sx q h; dsimp [e] at hh; omega
    · have hh := addAt_private e p y q q h; dsimp [e] at hh; omega
    · have hh := mulAt_private e sx y q q h; dsimp [e] at hh; omega
  have hext : KDerivation (imp (domainAt e x).encode (imp (domainAt e y).encode
      (imp (domainAt e p).encode (imp R (imp D
        (imp (mulAt e x y p).encode (existsCode q W.encode))))))) := by
    simpa [CutExtension, A,q,e,x,y,p,sx,R,W] using extension
  change KDerivation (imp T (imp U (imp V (imp R (imp D (imp S E.encode))))))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [S,D,R,V,U,T]
  have hS : Context Γ S := .head _ _
  have hD : Context Γ D := .hypothesis (by simp [Γ])
  have hR : Context Γ R := .hypothesis (by simp [Γ])
  have hV : Context Γ V := .hypothesis (by simp [Γ])
  have hU : Context Γ U := .hypothesis (by simp [Γ])
  have hT : Context Γ T := .hypothesis (by simp [Γ])
  have hpair : Context Γ (both (domainAt e p).encode (mulAt e x y p).encode) := by
    simpa [V, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using hV
  have hdx : Context Γ (domainAt e x).encode := .mp hT (.closed (termGraph_domain id t x e))
  have hdy : Context Γ (domainAt e y).encode := .mp hU (.closed (termGraph_domain id u y e))
  have hq : Context Γ (existsCode q W.encode) :=
    .mp (Context.conjunctionRight hpair) (.mp hD (.mp hR (.mp (Context.conjunctionLeft hpair)
      (.mp hdy (.mp hdx (.closed hext))))))
  have hctx : ∀ h, h ∈ Γ → KDerivation (imp h (allCode q h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases a : h = S
    · subst h; exact vS
    by_cases a : h = D
    · subst h; exact vD
    by_cases a : h = R
    · subst h; exact vR
    by_cases a : h = V
    · subst h; exact vV
    by_cases a : h = U
    · subst h; exact vU
    have a : h = T := by simpa [*] using hh
    subst h; exact vT
  have hpoint : Context Γ (imp W.encode E.encode) := by
    apply Context.deduction
    let Δ := [W.encode,S,D,R,V,U,T]
    have hw : Context Δ W.encode := .head _ _
    have hboth : Context Δ (both (domainAt e q).encode (both (literalCutAt e p y q).encode
        (both (addAt e p y q).encode (mulAt e sx y q).encode))) := by
      simpa [W, cutOutput, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using hw
    have hdomain := Context.conjunctionLeft hboth
    have hc := Context.conjunctionRight hboth
    have hrest := Context.conjunctionRight hc
    have hadd := Context.conjunctionLeft hrest
    have hmul := Context.conjunctionRight hrest
    have hS' : Context Δ S := .hypothesis (by simp [Δ])
    have hD' : Context Δ D := .hypothesis (by simp [Δ])
    have htail := Context.conjunctionIntro hD' (Context.conjunctionIntro hdomain
      (Context.conjunctionIntro hS' (Context.conjunctionIntro hadd hmul)))
    have ht' : Context Δ F.encode := by
      simpa [F, tailBody, D,S, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using htail
    have hi := existsIntroduce q F hF
    have hr := Context.mp ht' (.closed hi)
    simpa [E, Formula.encode, existsCode] using hr
  have hfinal := contextual_exists_elim q W.encode E.encode hctx vE hpoint hq
  exact hfinal

end PASoundness.PAtoCompactFirstFactorCutContinuation

#print axioms PASoundness.PAtoCompactFirstFactorCutContinuation.cutOutput
#print axioms PASoundness.PAtoCompactFirstFactorCutContinuation.CutExtension
#print axioms PASoundness.PAtoCompactFirstFactorCutContinuation.continuation_from_cut
