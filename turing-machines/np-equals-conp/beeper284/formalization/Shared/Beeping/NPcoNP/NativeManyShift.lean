import Shared.Beeping.NPcoNP.NativeManySelectorReturn

/-! Exact literal state-13 shift on a supplied finite local pattern. -/
namespace Shared.Beeping.NPcoNP.NativeManyShift
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeManySelectorReturn
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

theorem row13_1 : machine.table.row 13 true = ⟨false,.right,17,false⟩ := by decide
theorem step13_1 (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 13 h t)=(cfg 17 (h+1) (clearAt h t),false) := by
  have hw : (⟨13,h,t⟩ : Config 284).write false=(clearAt h t) := rfl
  simp [cfg,Machine.step,ht,row13_1,Move.apply,hw]

theorem row17_1 : machine.table.row 17 true = ⟨true,.right,18,false⟩ := by decide
theorem step17_1 (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 17 h t)=(cfg 18 (h+1) t,false) := by
  have hw : (⟨17,h,t⟩ : Config 284).write true=t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row17_1,Move.apply,hw]

theorem row18_0 : machine.table.row 18 false = ⟨false,.right,19,false⟩ := by decide
theorem step18_0 (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 18 h t)=(cfg 19 (h+1) t,false) := by
  have hw : (⟨18,h,t⟩ : Config 284).write false=t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row18_0,Move.apply,hw]

theorem row19_0 : machine.table.row 19 false = ⟨false,.left,20,false⟩ := by decide
theorem step19_0 (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 19 h t)=(cfg 20 (h-1) t,false) := by
  have hw : (⟨19,h,t⟩ : Config 284).write false=t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row19_0,Move.apply,hw]

theorem row20_0 : machine.table.row 20 false = ⟨true,.left,21,false⟩ := by decide
theorem step20_0 (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 20 h t)=(cfg 21 (h-1) (setAt h t),false) := by
  have hw : (⟨20,h,t⟩ : Config 284).write true=(setAt h t) := rfl
  simp [cfg,Machine.step,ht,row20_0,Move.apply,hw]

theorem row21_1 : machine.table.row 21 true = ⟨false,.left,20,false⟩ := by decide
theorem step21_1 (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 21 h t)=(cfg 20 (h-1) (clearAt h t),false) := by
  have hw : (⟨21,h,t⟩ : Config 284).write false=(clearAt h t) := rfl
  simp [cfg,Machine.step,ht,row21_1,Move.apply,hw]

theorem row21_0 : machine.table.row 21 false = ⟨false,.left,23,false⟩ := by decide
theorem step21_0 (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 21 h t)=(cfg 23 (h-1) t,false) := by
  have hw : (⟨21,h,t⟩ : Config 284).write false=t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row21_0,Move.apply,hw]

/-- Shift a pair of marked cells one place right. The surrounding
zero cells guarantee that both sweeps finish; the complete tape is retained. -/
theorem shift_pair (x : Int) (t : Int → Bool)
    (left : t (x-1)=false) (h0 : t x=true) (h1 : t (x+1)=true)
    (h2 : t (x+2)=false) (h3 : t (x+3)=false) :
    silentSegment machine (cfg 13 x t)
      (cfg 23 (x-2) (setAt (x+2) (clearAt (x+1) t))) 8 := by
  let t1 := clearAt x t
  let t2 := setAt (x+2) t1
  let t3 := clearAt (x+1) t2
  let t4 := setAt x t3
  have r1 : t1 (x+1)=true := by simp [t1,clearAt,show x+1≠x by omega,h1]
  have r2 : t1 (x+2)=false := by simp [t1,clearAt,show x+2≠x by omega,h2]
  have r3 : t1 (x+3)=false := by simp [t1,clearAt,show x+3≠x by omega,h3]
  have r4 : t2 (x+1)=true := by simp [t2,setAt,show x+1≠x+2 by omega,r1]
  have r5 : t3 x=false := by
    simp [t3,t2,t1,clearAt,setAt,show x≠x+1 by omega,show x≠x+2 by omega]
  have r6 : t4 (x-1)=false := by
    simp [t4,t3,t2,t1,clearAt,setAt,show x-1≠x by omega,
      show x-1≠x+1 by omega,show x-1≠x+2 by omega,left]
  have s1 := oneSeg machine _ _ (step13_1 x t h0)
  have s2 := oneSeg machine _ _ (step17_1 (x+1) t1 r1)
  have s3 := oneSeg machine _ _ (step18_0 (x+2) t1 r2)
  have s4 := oneSeg machine _ _ (step19_0 (x+3) t1 r3)
  have s5 := oneSeg machine _ _ (step20_0 (x+2) t1 r2)
  have s6 := oneSeg machine _ _ (step21_1 (x+1) t2 r4)
  have s7 := oneSeg machine _ _ (step20_0 x t3 r5)
  have s8 := oneSeg machine _ _ (step21_0 (x-1) t4 r6)
  have tape_eq : t4=setAt (x+2) (clearAt (x+1) t) := by
    funext p
    by_cases a : p=x
    · subst p; simp [t4,t3,t2,t1,setAt,clearAt,h0,show x≠x+1 by omega,show x≠x+2 by omega]
    · by_cases b : p=x+1
      · subst p; simp [t4,t3,t2,t1,setAt,clearAt,show x+1≠x by omega,show x+1≠x+2 by omega]
      · by_cases c : p=x+2
        · subst p; simp [t4,t3,t2,t1,setAt,clearAt,show x+2≠x by omega,show x+2≠x+1 by omega]
        · simp [t4,t3,t2,t1,setAt,clearAt,a,b,c]
  have p1 := segAdd machine _ _ _ 1 1 s1 s2
  have p2 := segAdd machine _ _ _ 2 1 (by simpa [Int.add_assoc] using p1) s3
  have p3 := segAdd machine _ _ _ 3 1 (by simpa [Int.add_assoc] using p2) s4
  have p4 := segAdd machine _ _ _ 4 1 (by simpa [Int.add_assoc,show x+3-1=x+2 by omega] using p3) s5
  have p5 := segAdd machine _ _ _ 5 1 (by simpa [Int.add_assoc,show x+2-1=x+1 by omega] using p4) s6
  have p6 := segAdd machine _ _ _ 6 1 (by simpa [Int.add_assoc,show x+1-1=x by omega] using p5) s7
  have p7 := segAdd machine _ _ _ 7 1 (by simpa [Int.add_assoc] using p6) s8
  simpa [Int.add_assoc,tape_eq,show x-1-1=x-2 by omega] using p7

/-- From state 15, both bounded scans and the subsequent pair shift
complete with no events. The supplied pattern includes the stopping zeros. -/
theorem scans_and_shift (p n : Nat) (h : Int) (t : Int → Bool)
    (first : Holds t h (List.replicate p true ++ [false]))
    (second : Holds t (h+(p : Int)+1) (List.replicate n true ++ [false]))
    (left : t (h+(p : Int)+(n : Int)+1)=false)
    (a : t (h+(p : Int)+(n : Int)+2)=true)
    (b : t (h+(p : Int)+(n : Int)+3)=true)
    (c : t (h+(p : Int)+(n : Int)+4)=false)
    (d : t (h+(p : Int)+(n : Int)+5)=false) :
    let x := h+(p : Int)+(n : Int)+2
    silentSegment machine (cfg 15 h t)
      (cfg 23 (x-2) (setAt (x+2) (clearAt (x+1) t))) (p+n+10) := by
  dsimp only
  let x := h+(p : Int)+(n : Int)+2
  have s1 := scan15 p h t first
  have s2 := scan11 n (h+(p : Int)+1) t second
  have s3 : silentSegment machine (cfg 13 x t)
      (cfg 23 (x-2) (setAt (x+2) (clearAt (x+1) t))) 8 := by
    apply shift_pair x t
    all_goals dsimp [x] <;> first | assumption | (convert left using 1 <;> congr 1 <;> omega) |
      (convert a using 1 <;> congr 1 <;> omega) | (convert b using 1 <;> congr 1 <;> omega) |
      (convert c using 1 <;> congr 1 <;> omega) | (convert d using 1 <;> congr 1 <;> omega)
  have s12 := segAdd machine _ _ _ (p+1) (n+1) s1 s2
  have s12' : silentSegment machine (cfg 15 h t) (cfg 13 x t) (p+1+(n+1)) := by
    have he : h+(p : Int)+1+(n : Int)+1=x := by dsimp [x]; omega
    simpa only [he] using s12
  have sall := segAdd machine _ _ _ (p+1+(n+1)) 8 s12' s3
  simpa [x,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using sall

#print axioms shift_pair
#print axioms scans_and_shift
end Shared.Beeping.NPcoNP.NativeManyShift
