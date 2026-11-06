import Shared.Beeping.NPcoNP.Source284CertificateProbeRun
import Shared.Beeping.NPcoNP.Source284WitnessScratch

/-! Cross the two sentinels and the two tag cells, handing the actual witness
frame to a supplied finite continuation. The original input-side stream is
retained on the opposite tape. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284CertificatePackSeek

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig run_front)
open Shared.Beeping.NPcoNP.Source284CertificateProbeRun (body)

def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q=0 then ⟨true,true,some 1⟩
  else if q=1 then ⟨b,false,some (if b then 2 else 1)⟩
  else if q=2 then ⟨b,false,some (if b then 3 else 2)⟩
  else if q=3 then ⟨b,false,some 4⟩
  else if q=4 then ⟨b,false,some 5⟩
  else shiftRow 5 (continuation (q-5) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (5+states) (table continuation) := by
  intro q hq b q' hnext
  by_cases hs : q<5
  · interval_cases q <;> cases b <;> simp [table] at hnext <;> omega
  · have he : (shiftRow 5 (continuation (q-5) b)).next=some q' := by
      simpa [table,show q ≠ 0 by omega,show q ≠ 1 by omega,show q ≠ 2 by omega,
        show q ≠ 3 by omega,show q ≠ 4 by omega] using hnext
    cases hh : (continuation (q-5) b).next with
    | none => simp [shiftRow,hh] at he
    | some r =>
      have hr := hv (q-5) (by omega) b r hh
      simp [shiftRow,hh] at he; subst q'; omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (5+q) b = shiftRow 5 (continuation q b) := by
  simp [table,show 5+q ≠ 1 by omega,show 5+q ≠ 2 by omega,show 5+q ≠ 3 by omega,
    show 5+q ≠ 4 by omega]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 5 c) = shiftConfig 5 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 5 c) fuel = shiftConfig 5 (run continuation c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

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

def seekCost (z1 z2 : Nat) := z1+z2+5

def inputSide (z1 z2 stream : Nat) :=
  4*(2*(2^z2*(2*(2^z1*(2*stream+1))+1))+1)

/-- Paid scan to the frame boundary. The two skipped tag cells are zero. -/
theorem seek (continuation : Nat → Bool → Row) (z1 z2 frame stream : Nat) :
    run (table continuation) ⟨body z1 z2 frame,2*stream,some 0⟩ (seekCost z1 z2) =
      ⟨inputSide z1 z2 stream,frame,some 5⟩ := by
  have h0 : step (table continuation) ⟨body z1 z2 frame,2*stream,some 0⟩ =
      ⟨2*stream+1,body z1 z2 frame,some 1⟩ := by simp [step,table,bit,Nat.testBit_zero]
  have h1 : table continuation 1 false = ⟨false,false,some 1⟩ := rfl
  have h2 : table continuation 2 false = ⟨false,false,some 2⟩ := rfl
  have ht : seekCost z1 z2 = 1+(z1+(1+(z2+(1+2)))) := by simp [seekCost]; omega
  rw [ht,Source284ScratchScanner.run_add]
  change run (table continuation) (step (table continuation)
    ⟨body z1 z2 frame,2*stream,some 0⟩) _ = _
  rw [h0]
  unfold body
  rw [Source284ScratchScanner.run_add,zeros _ 1 z1 _ _ h1,Source284ScratchScanner.run_add]
  change run (table continuation) (step (table continuation)
    ⟨2^z1*(2*stream+1),2*(2^z2*(2*(4*frame)+1))+1,some 1⟩) _ = _
  have hs1 : step (table continuation)
      ⟨2^z1*(2*stream+1),2*(2^z2*(2*(4*frame)+1))+1,some 1⟩ =
      ⟨2*(2^z1*(2*stream+1))+1,2^z2*(2*(4*frame)+1),some 2⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega
  rw [hs1,Source284ScratchScanner.run_add,zeros _ 2 z2 _ _ h2,Source284ScratchScanner.run_add]
  change run (table continuation) (step (table continuation)
    ⟨2^z2*(2*(2^z1*(2*stream+1))+1),2*(4*frame)+1,some 2⟩) 2 = _
  have hs2 (left : Nat) : step (table continuation) ⟨left,2*(4*frame)+1,some 2⟩ =
      ⟨2*left+1,4*frame,some 3⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega
  have hs3 (left : Nat) : step (table continuation) ⟨left,4*frame,some 3⟩ =
      ⟨2*left,2*frame,some 4⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.mul_mod] <;> omega
  have hs4 (left : Nat) : step (table continuation) ⟨left,2*frame,some 4⟩ =
      ⟨2*left,frame,some 5⟩ := by simp [step,table,bit,Nat.testBit_zero]
  simp only [hs2,run,hs3,hs4,inputSide]
  congr 1 <;> ring

theorem seek_then (continuation : Nat → Bool → Row) (z1 z2 frame stream fuel : Nat) :
    run (table continuation) ⟨body z1 z2 frame,2*stream,some 0⟩ (seekCost z1 z2+fuel) =
    shiftConfig 5 (run continuation ⟨inputSide z1 z2 stream,frame,some 0⟩ fuel) := by
  rw [Source284ScratchScanner.run_add,seek]
  change run (table continuation)
    (shiftConfig 5 ⟨inputSide z1 z2 stream,frame,some 0⟩) fuel = _
  exact relocated_run continuation _ fuel

end Shared.Beeping.NPcoNP.Source284CertificatePackSeek
