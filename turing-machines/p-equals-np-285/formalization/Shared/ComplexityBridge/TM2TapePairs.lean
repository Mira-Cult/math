import Shared.ComplexityBridge.TM2If
import Shared.ComplexityBridge.TM2BoundedWitnessGuard
import Shared.ComplexityBridge.TM2FixedRows
import Shared.ComplexityBridge.CircuitTapeMove

set_option backward.isDefEq.respectTransparency false

/-! Build the tape movement's wire pairs from a unary window and a binary
index. All comparisons enumerate only the supplied unary window. -/
namespace Shared.ComplexityBridge.TM2TapePairs
open Shared.ComplexityBridge

abbrev Input := List Bool × Nat

def pairAt (p : Input) : Nat × Nat :=
  let n := p.1.length
  let i := p.2
  let width := CircuitTapeMove.width n
  let low := TM2BoundedWitnessGuard.guard (p.1,i)
  let lowNext := TM2BoundedWitnessGuard.guard (p.1,i+1)
  let high := TM2BoundedWitnessGuard.guard (p.1++p.1,i)
  let nonzero := TM2BoundedWitnessGuard.numericNe (n,0)
  let ine0 := TM2BoundedWitnessGuard.numericNe (i,0)
  let ineN := TM2BoundedWitnessGuard.numericNe (i,n)
  let ineNext := TM2BoundedWitnessGuard.numericNe (i,n+1)
  if low then
    (if lowNext then i+3 else width, if ine0 then i+1 else 0)
  else if ineN then
    (if ineNext then i+1 else 0, if high then i+3 else width)
  else
    (if nonzero then 2 else width, if nonzero then n+3 else width)

theorem guard_eq_decide (tokens : List Bool) (i : Nat) :
    TM2BoundedWitnessGuard.guard (tokens,i) = decide (i < tokens.length) := by
  apply Bool.eq_iff_iff.mpr
  rw [TM2BoundedWitnessGuard.guard_correct]
  simp

theorem pairAt_correct (tokens : List Bool) (i : Nat) :
    pairAt (tokens,i) = CircuitTapeMove.pairAt tokens.length i := by
  simp only [pairAt,guard_eq_decide,List.length_append,TM2BoundedWitnessGuard.numericNe,
    decide_eq_true_eq]
  unfold CircuitTapeMove.pairAt CircuitTapeMove.width
  split_ifs <;> simp_all <;> (try split_ifs) <;> (try simp_all) <;> omega

theorem pairAt_isPolyTime : ComplexityTheory.IsPolyTime pairAt := by
  let tokens : Input → List Bool := fun p => p.1
  let i : Input → Nat := fun p => p.2
  let n : Input → Nat := fun p => p.1.length
  let zero : Input → Nat := fun _ => 0
  let two : Input → Nat := fun _ => 2
  let i1 : Input → Nat := fun p => i p+1
  let i3 : Input → Nat := fun p => i p+3
  let n1 : Input → Nat := fun p => n p+1
  let n3 : Input → Nat := fun p => n p+3
  let width : Input → Nat := fun p => 2*n p+3
  let doubled : Input → List Bool := fun p => tokens p++tokens p
  let low : Input → Bool := fun p => TM2BoundedWitnessGuard.guard (tokens p,i p)
  let lowNext : Input → Bool := fun p => TM2BoundedWitnessGuard.guard (tokens p,i1 p)
  let high : Input → Bool := fun p => TM2BoundedWitnessGuard.guard (doubled p,i p)
  let nz : Input → Bool := fun p => TM2BoundedWitnessGuard.numericNe (n p,zero p)
  let iz : Input → Bool := fun p => TM2BoundedWitnessGuard.numericNe (i p,zero p)
  let inn : Input → Bool := fun p => TM2BoundedWitnessGuard.numericNe (i p,n p)
  let inext : Input → Bool := fun p => TM2BoundedWitnessGuard.numericNe (i p,n1 p)
  let ly : Input → Nat := fun p => if lowNext p then i3 p else width p
  let ln : Input → Nat := fun p => if iz p then i1 p else zero p
  let ry : Input → Nat := fun p => if inext p then i1 p else zero p
  let rn : Input → Nat := fun p => if high p then i3 p else width p
  let cy : Input → Nat := fun p => if nz p then two p else width p
  let cn : Input → Nat := fun p => if nz p then n3 p else width p
  let l : Input → Nat × Nat := fun p => (ly p,ln p)
  let r : Input → Nat × Nat := fun p => (ry p,rn p)
  let c : Input → Nat × Nat := fun p => (cy p,cn p)
  let rc : Input → Nat × Nat := fun p => if inn p then r p else c p
  have ht : ComplexityTheory.IsPolyTime tokens := TM2PairFirst.first_isPolyTime
  have hi : ComplexityTheory.IsPolyTime i := TM2GuardAllStep.second_isPolyTime
  have hn : ComplexityTheory.IsPolyTime n := TM2Compose.isPolyTime_comp tokens List.length ht TM2BinaryListLength.length_isPolyTime
  have hz : ComplexityTheory.IsPolyTime zero := TM2EmptyConstant.zero_isPolyTime
  have htwo : ComplexityTheory.IsPolyTime two := TM2Compose.isPolyTime_comp zero (fun x => x+2) hz (TM2FixedRows.addFixed_isPolyTime 2)
  have hi1 : ComplexityTheory.IsPolyTime i1 := TM2Compose.isPolyTime_comp i (fun x => x+1) hi (TM2FixedRows.addFixed_isPolyTime 1)
  have hi3 : ComplexityTheory.IsPolyTime i3 := TM2Compose.isPolyTime_comp i (fun x => x+3) hi (TM2FixedRows.addFixed_isPolyTime 3)
  have hn1 : ComplexityTheory.IsPolyTime n1 := TM2Compose.isPolyTime_comp n (fun x => x+1) hn (TM2FixedRows.addFixed_isPolyTime 1)
  have hn3 : ComplexityTheory.IsPolyTime n3 := TM2Compose.isPolyTime_comp n (fun x => x+3) hn (TM2FixedRows.addFixed_isPolyTime 3)
  have hdbl : ComplexityTheory.IsPolyTime (fun p : Input => 2*n p) := TM2Compose.isPolyTime_comp n (fun x => 2*x) hn CNFBinaryIndex.double_isPolyTime
  have hw : ComplexityTheory.IsPolyTime width := TM2Compose.isPolyTime_comp (fun p : Input => 2*n p) (fun x => x+3) hdbl (TM2FixedRows.addFixed_isPolyTime 3)
  have hdt := TM2GuardAllStep.pair_isPolyTime tokens tokens ht ht
  have hd : ComplexityTheory.IsPolyTime doubled := TM2Compose.isPolyTime_comp (fun p => (tokens p,tokens p)) (TM2ListAppend.append (α := Bool)) hdt TM2ListAppend.append_isPolyTime
  have hlo : ComplexityTheory.IsPolyTime low := TM2Compose.isPolyTime_comp (fun p => (tokens p,i p)) TM2BoundedWitnessGuard.guard
    (TM2GuardAllStep.pair_isPolyTime tokens i ht hi) TM2BoundedWitnessGuard.guard_isPolyTime
  have hln : ComplexityTheory.IsPolyTime lowNext := TM2Compose.isPolyTime_comp (fun p => (tokens p,i1 p)) TM2BoundedWitnessGuard.guard
    (TM2GuardAllStep.pair_isPolyTime tokens i1 ht hi1) TM2BoundedWitnessGuard.guard_isPolyTime
  have hhigh : ComplexityTheory.IsPolyTime high := TM2Compose.isPolyTime_comp (fun p => (doubled p,i p)) TM2BoundedWitnessGuard.guard
    (TM2GuardAllStep.pair_isPolyTime doubled i hd hi) TM2BoundedWitnessGuard.guard_isPolyTime
  have hnz : ComplexityTheory.IsPolyTime nz := TM2Compose.isPolyTime_comp (fun p => (n p,zero p)) TM2BoundedWitnessGuard.numericNe
    (TM2GuardAllStep.pair_isPolyTime n zero hn hz) TM2BoundedWitnessGuard.numericNe_isPolyTime
  have hiz : ComplexityTheory.IsPolyTime iz := TM2Compose.isPolyTime_comp (fun p => (i p,zero p)) TM2BoundedWitnessGuard.numericNe
    (TM2GuardAllStep.pair_isPolyTime i zero hi hz) TM2BoundedWitnessGuard.numericNe_isPolyTime
  have hinn : ComplexityTheory.IsPolyTime inn := TM2Compose.isPolyTime_comp (fun p => (i p,n p)) TM2BoundedWitnessGuard.numericNe
    (TM2GuardAllStep.pair_isPolyTime i n hi hn) TM2BoundedWitnessGuard.numericNe_isPolyTime
  have hinext : ComplexityTheory.IsPolyTime inext := TM2Compose.isPolyTime_comp (fun p => (i p,n1 p)) TM2BoundedWitnessGuard.numericNe
    (TM2GuardAllStep.pair_isPolyTime i n1 hi hn1) TM2BoundedWitnessGuard.numericNe_isPolyTime
  have hly : ComplexityTheory.IsPolyTime ly := TM2If.if_isPolyTime lowNext i3 width hln hi3 hw
  have hln' : ComplexityTheory.IsPolyTime ln := TM2If.if_isPolyTime iz i1 zero hiz hi1 hz
  have hry : ComplexityTheory.IsPolyTime ry := TM2If.if_isPolyTime inext i1 zero hinext hi1 hz
  have hrn : ComplexityTheory.IsPolyTime rn := TM2If.if_isPolyTime high i3 width hhigh hi3 hw
  have hcy : ComplexityTheory.IsPolyTime cy := TM2If.if_isPolyTime nz two width hnz htwo hw
  have hcn : ComplexityTheory.IsPolyTime cn := TM2If.if_isPolyTime nz n3 width hnz hn3 hw
  have hl : ComplexityTheory.IsPolyTime l := TM2GuardAllStep.pair_isPolyTime ly ln hly hln'
  have hr : ComplexityTheory.IsPolyTime r := TM2GuardAllStep.pair_isPolyTime ry rn hry hrn
  have hc : ComplexityTheory.IsPolyTime c := TM2GuardAllStep.pair_isPolyTime cy cn hcy hcn
  have hrc : ComplexityTheory.IsPolyTime rc := TM2If.if_isPolyTime inn r c hinn hr hc
  have h := TM2If.if_isPolyTime low l rc hlo hl hrc
  have he : (fun p => if low p then l p else rc p) = pairAt := by
    funext p
    simp only [low,l,ly,ln,rc,inn,r,ry,rn,c,cy,cn,lowNext,high,iz,inext,nz,
      tokens,i,n,zero,two,i1,i3,n1,n3,width,doubled,pairAt,CircuitTapeMove.width]
    have hew : 2*p.1.length+3 = 3+2*p.1.length := by omega
    simp only [hew]
  rw [he] at h
  exact h

namespace Fixtures
example : pairAt ([],0) = (3,3) := rfl
example : pairAt ([true,true],0) = (3,0) := rfl
example : pairAt ([true,true],2) = (2,5) := rfl
example : pairAt ([true,true],4) = (5,7) := rfl
example : pairAt ([true,true],100) = (101,7) := rfl
end Fixtures
end Shared.ComplexityBridge.TM2TapePairs
