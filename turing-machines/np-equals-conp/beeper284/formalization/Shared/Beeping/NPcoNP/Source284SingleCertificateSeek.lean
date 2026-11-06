import Shared.Beeping.NPcoNP.Source284CertificatePackSeek

/-! Seek an actual tagged witness behind one delimiter and an arbitrary zero
gap. The gap length indexes the proof and clock; it is not supplied to the
finite source table. The entire input-side stream and frame suffix are kept. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284SingleCertificateSeek

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig run_front)

/-- Reuse the five-state two-delimiter seeker, redirecting its first marker
directly to the existing two tag-cell steps. -/
def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q=1 ∧ b then ⟨true,false,some 3⟩
  else Source284CertificatePackSeek.table continuation q b

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (5+states) (table continuation) := by
  intro q hq b q' hnext
  by_cases h : q=1 ∧ b=true
  · obtain ⟨rfl,rfl⟩ := h; simp [table] at hnext; omega
  · have he : (Source284CertificatePackSeek.table continuation q b).next=some q' := by
      simpa [table,h] using hnext
    exact Source284CertificatePackSeek.closed states continuation hn hv q hq b q' he

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (5+q) b = shiftRow 5 (continuation q b) := by
  simp [table,Source284CertificatePackSeek.relocated_row,show 5+q ≠ 1 by omega]

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

theorem zeros (continuation : Nat → Bool → Row) (count left right : Nat) :
    run (table continuation) ⟨left,2^count*right,some 1⟩ count =
      ⟨2^count*left,right,some 1⟩ := by
  induction count generalizing left with
  | zero => simp [run]
  | succ count ih =>
    rw [pow_succ]
    have he : (2^count*2)*right = 2*(2^count*right) := by ring
    rw [he,run_front]
    have hs : step (table continuation) ⟨left,2*(2^count*right),some 1⟩ =
        ⟨2*left,2^count*right,some 1⟩ := by
      simp [step,table,Source284CertificatePackSeek.table,Nat.testBit_zero,bit]
    rw [hs,ih]
    congr 1 <;> ring

def seekCost (zeros : Nat) : Nat := zeros+4
def inputSide (zeros stream : Nat) : Nat := 4*(2*(2^zeros*(2*stream+1))+1)

/-- The marker and both zero tag bits are traversed in finite source time. -/
theorem seek (continuation : Nat → Bool → Row) (zeros frame stream : Nat) :
    run (table continuation) ⟨2^zeros*(2*(4*frame)+1),2*stream,some 0⟩ (seekCost zeros) =
      ⟨inputSide zeros stream,frame,some 5⟩ := by
  have ht : seekCost zeros = 1+(zeros+(1+2)) := by simp [seekCost]; omega
  rw [ht,Source284ScratchScanner.run_add]
  have h0 : step (table continuation) ⟨2^zeros*(2*(4*frame)+1),2*stream,some 0⟩ =
      ⟨2*stream+1,2^zeros*(2*(4*frame)+1),some 1⟩ := by
    simp [step,table,Source284CertificatePackSeek.table,bit,Nat.testBit_zero]
  change run (table continuation) (step (table continuation)
    ⟨2^zeros*(2*(4*frame)+1),2*stream,some 0⟩) _ = _
  rw [h0,Source284ScratchScanner.run_add,Source284SingleCertificateSeek.zeros,Source284ScratchScanner.run_add]
  have h1 (left : Nat) : step (table continuation) ⟨left,2*(4*frame)+1,some 1⟩ =
      ⟨2*left+1,4*frame,some 3⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega
  have h3 (left : Nat) : step (table continuation) ⟨left,4*frame,some 3⟩ =
      ⟨2*left,2*frame,some 4⟩ := by
    simp [step,table,Source284CertificatePackSeek.table,bit,Nat.testBit_zero,Nat.mul_mod] <;> omega
  have h4 (left : Nat) : step (table continuation) ⟨left,2*frame,some 4⟩ =
      ⟨2*left,frame,some 5⟩ := by
    simp [step,table,Source284CertificatePackSeek.table,bit,Nat.testBit_zero]
  simp only [h1,run,h3,h4,inputSide]
  congr 1 <;> ring

theorem seek_then (continuation : Nat → Bool → Row) (zeros frame stream fuel : Nat) :
    run (table continuation) ⟨2^zeros*(2*(4*frame)+1),2*stream,some 0⟩
      (seekCost zeros+fuel) =
    shiftConfig 5 (run continuation ⟨inputSide zeros stream,frame,some 0⟩ fuel) := by
  rw [Source284ScratchScanner.run_add,seek]
  change run (table continuation) (shiftConfig 5 ⟨inputSide zeros stream,frame,some 0⟩) fuel = _
  exact relocated_run continuation _ fuel

namespace Fixtures
def loop (_ : Nat) (b : Bool) : Row := ⟨b,false,some 0⟩
example : run (table loop) ⟨9,0,some 0⟩ 4 = ⟨12,1,some 5⟩ := by decide +kernel
example : run (table loop) ⟨36,6,some 0⟩ 6 = ⟨228,1,some 5⟩ := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284SingleCertificateSeek
