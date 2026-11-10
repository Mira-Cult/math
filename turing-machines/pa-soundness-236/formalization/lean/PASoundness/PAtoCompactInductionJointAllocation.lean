import PASoundness.PAtoCompactInductionJointLowAllocation
import PASoundness.PAtoCompactInductionJointHighAllocation
import PASoundness.PAtoCompactInductionJointNumericAllocation
import PASoundness.PAtoCompactInductionJointSelectorFreshness
import PASoundness.PAtoCompactInductionGlobalNumericNames

/-! A shared source-dependent allocation for the qfree induction engine,
zero-base and step interfaces. This theorem assembles syntactic freshness and
allocation witnesses; it is not a K proof or the induction axiom. -/
namespace PASoundness.PAtoCompactInductionJointAllocation
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactGuardedAllElim
open PASoundness.PAtoCompactGuardedAllImp PASoundness.PAtoCompactGuardedAllImpAlignment
open PASoundness.PAtoCompactGuardedGeneralizationAlignment
open PASoundness.PAtoCompactDirectGeneralization PASoundness.PAtoCompactInductionAugmentedGuard
open PASoundness.PAtoCompactInductionJointLowAllocation PASoundness.PAtoCompactInductionJointHighAllocation
open PASoundness.PAtoCompactInductionJointNumericAllocation PASoundness.PAtoCompactInductionJointSelectorFreshness
open PASoundness.PAtoCompactInductionGlobalNumericNames PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactQuantifiedRefutation PASoundness.PAtoCompactAdjunction

def JointLow (φ : Peano.Formula) (x : Nat) : Prop :=
   let N := lowBound φ x
    let v := N+1
    let point := N+2
    let m := N+100
    let t := instanceBinder φ x m
    t = N+101 ∧ topName x φ < point ∧ point < t ∧ v < t ∧ m < t ∧
    point ∉ (originalChild φ x).names ∧
    point ∉ (Peano.inductionAxiom φ x).freeVarFinset ∧
    v ∉ (Peano.inductionAxiom φ x).freeVarFinset ∧
    m ∉ (Peano.inductionAxiom φ x).freeVarFinset ∧
    point ∉ (scopeAt φ x t).names ∧
    v ∉ (scopeAt φ x t).names ∧ m ∉ (scopeAt φ x t).names ∧
    t ∉ (scopeAt φ x t).binders

def JointHigh (φ : Peano.Formula) (x : Nat) : Prop :=
   let N := lowBound φ x
    let m := N+100
    let t := instanceBinder φ x m
    let f := scopeAt φ x t
    let B := highBase φ x
    let Y := B+100
    let point := B+101
    let gb := graphBase φ x
    N+101 < B ∧ f.names.sup id < B ∧ guardBase (Peano.inductionAxiom φ x) ≤ B ∧
    m < B ∧ Y ∉ f.names ∧ Y ∉ (Peano.inductionAxiom φ x).freeVarFinset ∧
    N+1 < gb ∧ m < gb ∧ guardBase (augmented (Peano.inductionAxiom φ x) (N+1)) ≤ gb ∧
    Y < filterPredicate Y t (neg f.encode) ∧
    B+5 ≠ adjunctionPredicate (N+2) point ∧ Y ≠ adjunctionPredicate (N+2) point

def JointNumeric (N B X : Nat) : Prop :=
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
    [X,bD,p,q,u,t,l,m,r].Nodup

def JointSelector (N B : Nat) (f : Formula) : Prop :=
   let X := N+2
    let v := N+1
    let m := N+100
    let t := N+101
    let Y := B+100
    let W := B+5
    let p := B+7
    let q := B+8
    let u := B+12
    let r := B+13
    let w := B+24
    let point := B+101
    let z := B+3
    let C := filterPredicate Y t (neg f.encode)
    C ∉ [X,u,m,r] ∧ C ∉ f.names ∧ v ≠ C ∧ r ≠ C ∧
    m ∉ (namedFilterGraph Y t f).names ∧
    C ∉ (namedAllBase t m z f).names ∧
    C ∉ (namedAllSteps Y t v m w p q f).names ∧
    C ∉ (namedAllClassification Y v m z w p q).names ∧
    Y ∉ (namedAllBase t m z f).names ∧
    Y ∉ (replace t X f).names ∧
    W ≠ adjunctionPredicate X point ∧ Y ≠ adjunctionPredicate X point

def JointAllNames (N B : Nat) : Prop :=
   [N+2, N+1, N+100, N+101, B+5, B+6, B+7, B+8, B+9, B+10, B+11, B+12, B+13, B+14, B+15, B+16, B+17, B+18, B+19, B+20, B+21, B+22, B+23, B+24, B+25, B+26, B+27, B+28, B+29, B+30, B+31, B+32, B+33, B+34, B+35, B+36, B+100, B+101].Nodup

/-- The four source-dependent conditions, 13 matched name lists, all 12
selector/context clauses, and a global distinctness list hold simultaneously.
The displayed formulas still need to be used by the actual K proof compiler. -/
theorem joint_allocation (φ : Peano.Formula) (x : Nat) :
    let N := lowBound φ x
    let B := highBase φ x
    let f := scopeAt φ x (N+101)
    JointLow φ x ∧ JointHigh φ x ∧ JointNumeric N B (N+2) ∧
      JointSelector N B f ∧ JointAllNames N B := by
  dsimp only
  have hlo : JointLow φ x := low_allocation φ x
  have hhi : JointHigh φ x := high_allocation φ x
  let N := lowBound φ x
  let B := highBase φ x
  let f := scopeAt φ x (N+101)
  have hlow := low_allocation φ x
  have hhigh := high_allocation φ x
  dsimp only at hlow hhigh
  obtain ⟨heq, htop, hpoint, hv, hm, horig, hpI, hvI, hmI, hpN, hvN, hmN, htbind⟩ := hlow
  obtain ⟨hB, hf, hguard, hmB, hYf, hYI, hgv, hgm, hgGuard, hfilter, hW, hY⟩ := hhigh
  have hb : N+101 < B := by simpa only [N,B] using hB
  have hname : f.names.sup id < B := by
    dsimp [f,N,B]
    rw [← heq]
    exact hf
  have hmf : N+100 ∉ f.names := by
    dsimp [f,N]
    rw [← heq]
    exact hmN
  have hnum : JointNumeric N B (N+2) := joint_numeric_freshness N B (N+2) rfl hb
  have hsel : JointSelector N B f := joint_selector_context_freshness N B f hb hname hmf
  have hall : JointAllNames N B := names_nodup N B hb
  exact ⟨hlo, hhi, hnum, hsel, hall⟩
end PASoundness.PAtoCompactInductionJointAllocation

#print axioms PASoundness.PAtoCompactInductionJointAllocation.joint_allocation
