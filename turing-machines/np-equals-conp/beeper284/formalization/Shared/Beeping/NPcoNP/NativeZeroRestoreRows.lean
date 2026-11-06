import Shared.Beeping.NPcoNP.NativeFirstBankTouch
import Shared.Beeping.NPcoNP.NativeHalfOddReturn

/-! Literal states 262/263 and 268/269 implement a finite round trip between
explicit double-zero boundaries. The selected zero block's marker is restored
at state 25. The window hypotheses are supplied; their relation to a particular
blank-start run is a separate theorem. -/
namespace Shared.Beeping.NPcoNP.NativeZeroRestore
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

theorem row262_zero : machine.table.row 262 false=⟨false,.left,263,false⟩ := by decide
theorem row262_one : machine.table.row 262 true=⟨true,.left,262,false⟩ := by decide
theorem row263_zero : machine.table.row 263 false=⟨false,.left,264,false⟩ := by decide
theorem row263_one : machine.table.row 263 true=⟨true,.left,262,false⟩ := by decide
theorem row264_one : machine.table.row 264 true=⟨false,.right,49,false⟩ := by decide
theorem row49_zero : machine.table.row 49 false=⟨false,.right,267,false⟩ := by decide
theorem row267_zero : machine.table.row 267 false=⟨true,.right,268,false⟩ := by decide
theorem row268_zero : machine.table.row 268 false=⟨false,.right,269,false⟩ := by decide
theorem row268_one : machine.table.row 268 true=⟨true,.right,268,false⟩ := by decide
theorem row269_zero : machine.table.row 269 false=⟨false,.right,17,false⟩ := by decide
theorem row269_one : machine.table.row 269 true=⟨true,.right,268,false⟩ := by decide
theorem row17_zero : machine.table.row 17 false=⟨false,.left,13,false⟩ := by decide
theorem row13_zero : machine.table.row 13 false=⟨true,.left,25,false⟩ := by decide

theorem step262_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 262 h t)=(cfg 263 (h-1) t,false) := by
  have hw : (⟨262,h,t⟩ : Config 284).write false=t := by rw [←ht]; exact write_current _
  simp [cfg,Machine.step,ht,row262_zero,Move.apply,hw]

theorem step262_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 262 h t)=(cfg 262 (h-1) t,false) := by
  have hw : (⟨262,h,t⟩ : Config 284).write true=t := by rw [←ht]; exact write_current _
  simp [cfg,Machine.step,ht,row262_one,Move.apply,hw]

theorem step263_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 263 h t)=(cfg 264 (h-1) t,false) := by
  have hw : (⟨263,h,t⟩ : Config 284).write false=t := by rw [←ht]; exact write_current _
  simp [cfg,Machine.step,ht,row263_zero,Move.apply,hw]

theorem step263_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 263 h t)=(cfg 262 (h-1) t,false) := by
  have hw : (⟨263,h,t⟩ : Config 284).write true=t := by rw [←ht]; exact write_current _
  simp [cfg,Machine.step,ht,row263_one,Move.apply,hw]

theorem step264_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 264 h t)=(cfg 49 (h+1) (clearAt h t),false) := by
  have hw : (⟨264,h,t⟩ : Config 284).write false=clearAt h t := rfl
  simp [cfg,Machine.step,ht,row264_one,Move.apply,hw]

theorem step49_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 49 h t)=(cfg 267 (h+1) t,false) := by
  have hw : (⟨49,h,t⟩ : Config 284).write false=t := by rw [←ht]; exact write_current _
  simp [cfg,Machine.step,ht,row49_zero,Move.apply,hw]

theorem step267_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 267 h t)=(cfg 268 (h+1) (setAt h t),false) := by
  have hw : (⟨267,h,t⟩ : Config 284).write true=setAt h t := rfl
  simp [cfg,Machine.step,ht,row267_zero,Move.apply,hw]

theorem step268_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 268 h t)=(cfg 269 (h+1) t,false) := by
  have hw : (⟨268,h,t⟩ : Config 284).write false=t := by rw [←ht]; exact write_current _
  simp [cfg,Machine.step,ht,row268_zero,Move.apply,hw]

theorem step268_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 268 h t)=(cfg 268 (h+1) t,false) := by
  have hw : (⟨268,h,t⟩ : Config 284).write true=t := by rw [←ht]; exact write_current _
  simp [cfg,Machine.step,ht,row268_one,Move.apply,hw]

theorem step269_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 269 h t)=(cfg 17 (h+1) t,false) := by
  have hw : (⟨269,h,t⟩ : Config 284).write false=t := by rw [←ht]; exact write_current _
  simp [cfg,Machine.step,ht,row269_zero,Move.apply,hw]

theorem step269_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 269 h t)=(cfg 268 (h+1) t,false) := by
  have hw : (⟨269,h,t⟩ : Config 284).write true=t := by rw [←ht]; exact write_current _
  simp [cfg,Machine.step,ht,row269_one,Move.apply,hw]

theorem step17_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 17 h t)=(cfg 13 (h-1) t,false) := by
  have hw : (⟨17,h,t⟩ : Config 284).write false=t := by rw [←ht]; exact write_current _
  simp [cfg,Machine.step,ht,row17_zero,Move.apply,hw]

theorem step13_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 13 h t)=(cfg 25 (h-1) (setAt h t),false) := by
  have hw : (⟨13,h,t⟩ : Config 284).write true=setAt h t := rfl
  simp [cfg,Machine.step,ht,row13_zero,Move.apply,hw]


end Shared.Beeping.NPcoNP.NativeZeroRestore
