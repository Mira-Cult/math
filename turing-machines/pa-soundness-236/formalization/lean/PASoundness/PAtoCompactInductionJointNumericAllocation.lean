import Mathlib.Data.List.Nodup
import Mathlib.Tactic

/-! Simultaneous arithmetic name allocation for the restricted induction engine,
its quantifier-free step and zero-base interface. It establishes only numeric
bounds and distinctness; source/name freshness and selector conditions are
separate obligations. -/
namespace PASoundness.PAtoCompactInductionJointNumericAllocation

/-- If the source point is N+2 and the zero-graph allocation B is above
N+100, these offsets satisfy all six engine lists and all six qfree-step lists,
with engine t equal to the step subset binder and zero name B+3. -/
theorem joint_numeric_freshness (N B X : Nat) (hX : X = N+2) (hB : N+101 < B) :
    let m := N+100
    let v := N+1
    let t := N+101
    let Y := B+100
    let W := B+5
    let bD := B+6
    let p := B+7
    let q := B+8
    let d := B+9
    let s := B+10
    let T := B+11
    let u := B+12
    let r := B+13
    let U := B+14
    let l := B+15
    let R := B+16
    let Z := B+17
    let V := B+18
    let J := B+19
    let uD := B+20
    let tD := B+21
    let aD := B+22
    let sD := B+23
    let w := B+24
    let vA := B+25
    let hA := B+26
    let rA := B+27
    let sA := B+28
    let dA := B+29
    let eA := B+30
    let iA := B+31
    let uA := B+32
    let jA := B+33
    let nA := B+34
    let cA := B+35
    let oA := B+36
    let point := B+101
    let zeroName := B+3
    v < t ∧
    m < t ∧
    m < B ∧
    zeroName = B+3 ∧
    Y > zeroName ∧
    Y > X ∧
    point > Y ∧
    Y > W ∧
    [X,Y,W,bD,p,q,d,s,T,u,t,m,r,U,l,R,Z,V,J,point].Nodup ∧
    [Y,u,t,l,m,r,X].Nodup ∧
    [Y,t,X,u,m,r].Nodup ∧
    [m,p,q,uD,t,v,tD,w].Nodup ∧
    [Y,m,p,q,bD,aD,t,v,tD,uD,sD].Nodup ∧
    [Y,u,t,m,r,aD,v,tD].Nodup ∧
    [Y,v,bD,p,q,vA,u,t,l,hA,r,rA,sA].Nodup ∧
    [v,m,w,vA,p,q,dA,eA,iA,rA,t,hA,r,uA,l,jA,nA,cA,oA].Nodup ∧
    [Y,bD,p,q,u,t,l,hA,r,v].Nodup ∧
    [Y,bD,p,q,u,t,l,hA,r,m].Nodup ∧
    [Y,u,t,m,r,hA].Nodup ∧
    [Y,u,t,l,m,r,hA].Nodup ∧
    [X,bD,p,q,u,t,l,m,r].Nodup := by
  dsimp only
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, List.nodup_nil, and_true]
  (repeat' apply And.intro) <;> first | trivial | omega

end PASoundness.PAtoCompactInductionJointNumericAllocation

#print axioms PASoundness.PAtoCompactInductionJointNumericAllocation.joint_numeric_freshness
