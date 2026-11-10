import PASoundness.PAtoCompactFirstFactorDiamondVacuity

/-! A fixed-label proof transformer binds the witnesses of the explicitly
supplied first-factor diamond. No graph, product, or successor witness is
constructed here. -/
namespace PASoundness.PAtoCompactFirstFactorDiamondPoint

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFirstFactorDiamondVacuity

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The successor, sum, new-product, and two candidate conditions left after
extracting the two source graphs and old candidate product. -/
def tailBody (e x y p sx q : Nat) : Formula :=
  andF (domainAt e sx) (andF (domainAt e q) (andF (succAt e x sx)
    (andF (addAt e p y q) (mulAt e sx y q))))

/-- Given both source graphs, the old candidate product, and the remaining
pointwise conditions, package those exact objects into the five nested
existentials. This transformer does not assert any antecedent. -/
def point (t u : Peano.Term) (q : Nat) :
    let x := q+1
    let y := q+2
    let p := q+3
    let sx := q+4
    let e := q+100
    KDerivation (imp (termGraph id t x e).encode
      (imp (termGraph id u y e).encode
        (imp (andF (domainAt e p) (mulAt e x y p)).encode
          (imp (tailBody e x y p sx q).encode (closedDiamondF t u q).encode)))) := by
  let x := q+1
  let y := q+2
  let p := q+3
  let sx := q+4
  let e := q+100
  let T := (termGraph id t x e).encode
  let U := (termGraph id u y e).encode
  let V := (andF (domainAt e p) (mulAt e x y p)).encode
  let B := (tailBody e x y p sx q).encode
  let M := diamondF t u e x y p sx q
  have hq : q ∉ M.binders := diamond_not_binder t u e x y p sx q q (by dsimp [e]; omega)
  have hsx : sx ∉ M.binders := diamond_not_binder t u e x y p sx q sx (by dsimp [e,sx]; omega)
  have hp : p ∉ M.binders := diamond_not_binder t u e x y p sx q p (by dsimp [e,p]; omega)
  have hy : y ∉ M.binders := diamond_not_binder t u e x y p sx q y (by dsimp [e,y]; omega)
  have hx : x ∉ M.binders := diamond_not_binder t u e x y p sx q x (by dsimp [e,x]; omega)
  have hqI := existsIntroduce q M hq
  have hsxI := existsIntroduce sx (.ex q M) (by simpa [Formula.binders, sx] using hsx)
  have hpI := existsIntroduce p (.ex sx (.ex q M)) (by simpa [Formula.binders, p,sx] using hp)
  have hyI := existsIntroduce y (.ex p (.ex sx (.ex q M))) (by simpa [Formula.binders, y,p,sx] using hy)
  have hxI := existsIntroduce x (.ex y (.ex p (.ex sx (.ex q M))))
    (by simpa [Formula.binders, x,y,p,sx] using hx)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [B,V,U,T]
  have hb : Context Γ B := .head _ _
  have hv : Context Γ V := .hypothesis (by simp [Γ])
  have hu : Context Γ U := .hypothesis (by simp [Γ])
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hdSX := Context.conjunctionLeft hb
  have hrest := Context.conjunctionRight hb
  have hdQ := Context.conjunctionLeft hrest
  have hrest := Context.conjunctionRight hrest
  have hS := Context.conjunctionLeft hrest
  have hrest := Context.conjunctionRight hrest
  have hA := Context.conjunctionLeft hrest
  have hNew := Context.conjunctionRight hrest
  have hdP := Context.conjunctionLeft hv
  have hOld := Context.conjunctionRight hv
  have hM : Context Γ M.encode := by
    have h := Context.conjunctionIntro hdSX (Context.conjunctionIntro hdP
      (Context.conjunctionIntro hdQ (Context.conjunctionIntro ht
        (Context.conjunctionIntro hu (Context.conjunctionIntro hS
          (Context.conjunctionIntro hOld (Context.conjunctionIntro hA hNew)))))))
    simpa [M, diamondF, T,U,V,B,tailBody, andF, CompactNamed.Formula.not,
      Formula.encode,both,neg] using h
  have h1 := Context.mp hM (.closed hqI)
  have h2 := Context.mp h1 (.closed hsxI)
  have h3 := Context.mp h2 (.closed hpI)
  have h4 := Context.mp h3 (.closed hyI)
  have h5 := Context.mp h4 (.closed hxI)
  simpa [closedDiamondF,x,y,p,sx,e,M,Formula.encode,existsCode] using h5

end PASoundness.PAtoCompactFirstFactorDiamondPoint

#print axioms PASoundness.PAtoCompactFirstFactorDiamondPoint.tailBody
#print axioms PASoundness.PAtoCompactFirstFactorDiamondPoint.point
