import Shared.Beeping.NPcoNP.Source284TwoSidedScaledQuadraticWindow
import Shared.Beeping.NPcoNP.Source284WindowRewind

/-! A finite row table crosses both preserved token sentinels, reads the first
witness marker beyond two raw tag bits, and returns without changing either
tape half. The two sentinels and the marked scratch boundary control the
return; no numerical zero-run length is supplied to the table. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284CertificateProbe

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig run_front)

def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q=0 then ⟨true,true,some 1⟩
  else if q=1 then ⟨b,false,some (if b then 2 else 1)⟩
  else if q=2 then ⟨b,false,some (if b then 3 else 2)⟩
  else if q=3 then ⟨b,false,some 4⟩
  else if q=4 then ⟨b,false,some 5⟩
  else if q=5 then ⟨b,true,some (if b then 7 else 6)⟩
  else if q<10 then ⟨b,false,some (q+2)⟩
  else if q<12 then ⟨b,false,some (q+2)⟩
  else if q<14 then ⟨b,false,some (if b then q+2 else q)⟩
  else if q<16 then ⟨false,b,some (if b then q+2 else q)⟩
  else if q<18 then ⟨b,true,some (q+2)⟩
  else shiftRow 18 (continuation (q-18) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 2 ≤ states) (hv : Closed states continuation) : Closed (18+states) (table continuation) := by
  intro q hq b q' hnext
  by_cases hs : q<18
  · interval_cases q <;> cases b <;> simp [table] at hnext <;> omega
  · have he : (shiftRow 18 (continuation (q-18) b)).next=some q' := by
      simpa [table,show q ≠ 0 by omega,show q ≠ 1 by omega,show q ≠ 2 by omega,
        show q ≠ 3 by omega,show q ≠ 4 by omega,show q ≠ 5 by omega,
        show ¬ q<10 by omega,show ¬ q<12 by omega,show ¬ q<14 by omega,
        show ¬ q<16 by omega,show ¬ q<18 by omega] using hnext
    cases hh : (continuation (q-18) b).next with
    | none => simp [shiftRow,hh] at he
    | some r =>
      have hr := hv (q-18) (by omega) b r hh
      simp [shiftRow,hh] at he; subst q'; omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (18+q) b = shiftRow 18 (continuation q b) := by
  simp [table,show 18+q ≠ 1 by omega,show 18+q ≠ 2 by omega,show 18+q ≠ 3 by omega,
    show 18+q ≠ 4 by omega,show 18+q ≠ 5 by omega,show ¬ 18+q<10 by omega,
    show ¬ 18+q<12 by omega,show ¬ 18+q<14 by omega,show ¬ 18+q<16 by omega,show ¬ 18+q<18 by omega]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 18 c) = shiftConfig 18 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 18 c) fuel = shiftConfig 18 (run continuation c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

/-- Any zero-loop row transfers a prescribed finite run of zero cells. -/
theorem zeros (continuation : Nat → Bool → Row) (q count left right : Nat)
    (hrow : table continuation q false = ⟨false,false,some q⟩) :
    run (table continuation) ⟨left,2^count*right,some q⟩ count =
      ⟨2^count*left,right,some q⟩ := by
  induction count generalizing left with
  | zero => simp [run]
  | succ count ih =>
    rw [pow_succ]
    have he : (2^count*2)*right = 2*(2^count*right) := by ring
    rw [he,run_front]
    have hs : step (table continuation) ⟨left,2*(2^count*right),some q⟩ =
        ⟨2*left,2^count*right,some q⟩ := by
      simp [step,Nat.testBit_zero,hrow,bit]
    rw [hs,ih]
    congr 1 <;> ring

theorem start (continuation : Nat → Bool → Row) (left stream : Nat) :
    step (table continuation) ⟨left,2*stream,some 0⟩ = ⟨2*stream+1,left,some 1⟩ := by
  simp [step,table,bit,Nat.testBit_zero]

theorem first_marker (continuation : Nat → Bool → Row) (left right : Nat) :
    step (table continuation) ⟨left,2*right+1,some 1⟩ = ⟨2*left+1,right,some 2⟩ := by
  simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega

theorem second_marker (continuation : Nat → Bool → Row) (left right : Nat) :
    step (table continuation) ⟨left,2*right+1,some 2⟩ = ⟨2*left+1,right,some 3⟩ := by
  simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega

theorem read_and_return_two (continuation : Nat → Bool → Row) (left frame : Nat) :
    run (table continuation) ⟨left,4*frame,some 3⟩ 5 =
      ⟨4*frame,left,some (10+(if frame.testBit 0 then 1 else 0))⟩ := by
  have h3 : step (table continuation) ⟨left,4*frame,some 3⟩ = ⟨2*left,2*frame,some 4⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.mul_mod] <;> omega
  have h4 : step (table continuation) ⟨2*left,2*frame,some 4⟩ = ⟨4*left,frame,some 5⟩ := by
    simp [step,table,bit,Nat.testBit_zero] <;> omega
  have h5 : step (table continuation) ⟨4*left,frame,some 5⟩ =
      ⟨frame,4*left,some (6+(if frame.testBit 0 then 1 else 0))⟩ := by
    have hd : 2*(frame/2)+bit (frame.testBit 0)=frame := by
      rw [Source284WitnessScanner.lowbit_value]
      omega
    simp only [step,table,show (5:Nat) ≠ 0 by decide,show (5:Nat) ≠ 1 by decide,
      show (5:Nat) ≠ 2 by decide,show (5:Nat) ≠ 3 by decide,show (5:Nat) ≠ 4 by decide,
      ↓reduceIte]
    rw [hd]
    cases frame.testBit 0 <;> rfl
  have hb : (if frame.testBit 0 then 1 else 0) < 2 := by split <;> omega
  have h6 (mode : Nat) (hm : mode<2) : step (table continuation) ⟨frame,4*left,some (6+mode)⟩ =
      ⟨2*frame,2*left,some (8+mode)⟩ := by
    interval_cases mode <;> simp [step,table,bit,Nat.testBit_zero,Nat.mul_mod] <;> omega
  have h8 (mode : Nat) (hm : mode<2) : step (table continuation) ⟨2*frame,2*left,some (8+mode)⟩ =
      ⟨4*frame,left,some (10+mode)⟩ := by
    interval_cases mode <;> simp [step,table,bit,Nat.testBit_zero] <;> omega
  simp only [run,h3,h4,h5,h6 _ hb,h8 _ hb]

theorem return_first (continuation : Nat → Bool → Row) (mode left right : Nat) (hm : mode<2) :
    step (table continuation) ⟨left,2*right+1,some (10+mode)⟩ =
      ⟨2*left+1,right,some (12+mode)⟩ := by
  interval_cases mode <;> simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega

theorem return_second (continuation : Nat → Bool → Row) (mode left right : Nat) (hm : mode<2) :
    step (table continuation) ⟨left,2*right+1,some (12+mode)⟩ =
      ⟨2*left+1,right,some (14+mode)⟩ := by
  interval_cases mode <;> simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega

theorem finish (continuation : Nat → Bool → Row) (mode left stream : Nat) (hm : mode<2) :
    run (table continuation) ⟨left,2*stream+1,some (14+mode)⟩ 2 =
      ⟨left,2*stream,some (18+mode)⟩ := by
  interval_cases mode <;> simp [run,step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;>
    try split_ifs <;> omega

end Shared.Beeping.NPcoNP.Source284CertificateProbe
