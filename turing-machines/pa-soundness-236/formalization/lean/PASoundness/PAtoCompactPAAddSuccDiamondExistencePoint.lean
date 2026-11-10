import PASoundness.PAtoCompactPAAddSuccDiamondExistenceVacuity
import PASoundness.PAtoCompactPAAddSuccDynamicWitness

/-! Fixed-label pointwise packaging for the shared addition-successor diamond.
All term graphs and operation relations remain explicit K antecedents; this
module constructs no graph values and claims no PA axiom by itself. -/
namespace PASoundness.PAtoCompactPAAddSuccDiamondExistencePoint
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactPAAddSuccDiamondExistenceVacuity
open PASoundness.PAtoCompactPAAddSuccDynamicWitness
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] PASoundness.CompactProof.imp Cantor.pair Cantor.triangle

/-- For the canonical five witness labels, the two source graphs, an old
candidate sum, and the successor diamond yield the fully bound diamond. -/
def point (t u : Peano.Term) (q : Nat) :
    let x := q+1
    let y := q+2
    let z := q+3
    let sy := q+4
    let e := q+100
    KDerivation (imp (termGraph id t x e).encode
      (imp (termGraph id u y e).encode
        (imp (andF (domainAt e z) (addAt e x y z)).encode
          (imp (body e x y z sy q).encode (closedDiamondF t u q).encode)))) := by
  let x := q+1
  let y := q+2
  let z := q+3
  let sy := q+4
  let e := q+100
  let T := (termGraph id t x e).encode
  let U := (termGraph id u y e).encode
  let V := (andF (domainAt e z) (addAt e x y z)).encode
  let B := (body e x y z sy q).encode
  let M := diamondF t u e x y z sy q
  have hq : q ∉ M.binders := diamond_not_binder t u e x y z sy q q (by dsimp [e]; omega)
  have hsy : sy ∉ M.binders := diamond_not_binder t u e x y z sy q sy (by dsimp [e,sy]; omega)
  have hz : z ∉ M.binders := diamond_not_binder t u e x y z sy q z (by dsimp [e,z]; omega)
  have hy : y ∉ M.binders := diamond_not_binder t u e x y z sy q y (by dsimp [e,y]; omega)
  have hx : x ∉ M.binders := diamond_not_binder t u e x y z sy q x (by dsimp [e,x]; omega)
  have hqI := existsIntroduce q M hq
  have hsyI := existsIntroduce sy (.ex q M) (by simpa [Formula.binders, sy] using hsy)
  have hzI := existsIntroduce z (.ex sy (.ex q M)) (by simpa [Formula.binders, z,sy] using hz)
  have hyI := existsIntroduce y (.ex z (.ex sy (.ex q M))) (by simpa [Formula.binders, y,z,sy] using hy)
  have hxI := existsIntroduce x (.ex y (.ex z (.ex sy (.ex q M))))
    (by simpa [Formula.binders, x,y,z,sy] using hx)
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
  have hdsy := Context.conjunctionLeft hb
  have hrest := Context.conjunctionRight hb
  have hdq := Context.conjunctionLeft hrest
  have hrest := Context.conjunctionRight hrest
  have hs1 := Context.conjunctionLeft hrest
  have hrest := Context.conjunctionRight hrest
  have hs2 := Context.conjunctionLeft hrest
  have ha2 := Context.conjunctionRight hrest
  have hdz := Context.conjunctionLeft hv
  have ha1 := Context.conjunctionRight hv
  have hM : Context Γ M.encode := by
    have h := Context.conjunctionIntro hdsy (Context.conjunctionIntro hdz
      (Context.conjunctionIntro hdq (Context.conjunctionIntro ht
        (Context.conjunctionIntro hu (Context.conjunctionIntro hs1
          (Context.conjunctionIntro ha1 (Context.conjunctionIntro hs2 ha2)))))))
    simpa [M, diamondF, T,U,V,B,body, andF, CompactNamed.Formula.not,
      Formula.encode,both,neg] using h
  have h1 := Context.mp hM (.closed hqI)
  have h2 := Context.mp h1 (.closed hsyI)
  have h3 := Context.mp h2 (.closed hzI)
  have h4 := Context.mp h3 (.closed hyI)
  have h5 := Context.mp h4 (.closed hxI)
  simpa [closedDiamondF,x,y,z,sy,e,M,Formula.encode,existsCode] using h5

end PASoundness.PAtoCompactPAAddSuccDiamondExistencePoint
#print axioms PASoundness.PAtoCompactPAAddSuccDiamondExistencePoint.point
