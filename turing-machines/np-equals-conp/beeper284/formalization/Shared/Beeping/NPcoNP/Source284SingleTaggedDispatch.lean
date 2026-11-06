import Shared.Beeping.NPcoNP.Source284SingleCertificateSeek
import Shared.Beeping.NPcoNP.Source284TaggedWitnessCodec

/-! Inspect the two low tag bits after seeking the actual certificate
delimiter. The fixed table reaches continuation mode zero for tag `00` and
mode one for any other tag, in at most `gap+4` paid source steps. Mode one is
an explicit handoff, not an unbounded rejecting loop. Witness length and the
full controller remain separate obligations. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284SingleTaggedDispatch

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig run_front)

def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q=3 then ⟨b,false,some (if b then 6 else 4)⟩
  else if q=4 then ⟨b,false,some (if b then 6 else 5)⟩
  else Source284SingleCertificateSeek.table continuation q b

def mode (certificate : Nat) : Nat := if certificate%4=0 then 0 else 1

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 2 ≤ states) (hv : Closed states continuation) : Closed (5+states) (table continuation) := by
  intro q hq b q' hnext
  by_cases h3 : q=3
  · subst q; cases b <;> simp [table] at hnext <;> omega
  · by_cases h4 : q=4
    · subst q; cases b <;> simp [table,h3] at hnext <;> omega
    · have he : (Source284SingleCertificateSeek.table continuation q b).next=some q' := by
        simpa [table,h3,h4] using hnext
      exact Source284SingleCertificateSeek.closed states continuation (by omega) hv q hq b q' he

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (5+q) b = shiftRow 5 (continuation q b) := by
  simp [table,Source284SingleCertificateSeek.relocated_row,
    show 5+q ≠ 3 by omega,show 5+q ≠ 4 by omega]

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
      simp [step,table,Source284SingleCertificateSeek.table,
        Source284CertificatePackSeek.table,Nat.testBit_zero,bit]
    rw [hs,ih]
    congr 1 <;> ring

def boundary (zeros stream : Nat) : Nat := 2*(2^zeros*(2*stream+1))+1

/-- The delimiter is found without a runtime gap counter, leaving the two
tag bits at the current head and preserving the full certificate suffix. -/
theorem reach_tag (continuation : Nat → Bool → Row) (gap certificate stream : Nat) :
    run (table continuation) ⟨2^gap*(2*certificate+1),2*stream,some 0⟩ (gap+2) =
      ⟨boundary gap stream,certificate,some 3⟩ := by
  have ht : gap+2 = 1+(gap+1) := by omega
  rw [ht,Source284ScratchScanner.run_add]
  have h0 : step (table continuation) ⟨2^gap*(2*certificate+1),2*stream,some 0⟩ =
      ⟨2*stream+1,2^gap*(2*certificate+1),some 1⟩ := by
    simp [step,table,Source284SingleCertificateSeek.table,Source284CertificatePackSeek.table,
      bit,Nat.testBit_zero]
  change run (table continuation) (step (table continuation)
    ⟨2^gap*(2*certificate+1),2*stream,some 0⟩) _ = _
  rw [h0,Source284ScratchScanner.run_add,Source284SingleTaggedDispatch.zeros]
  change step (table continuation) ⟨2^gap*(2*stream+1),2*certificate+1,some 1⟩ = _
  simp [step,table,Source284SingleCertificateSeek.table,bit,Nat.testBit_zero,
    Nat.add_mod,Nat.mul_mod,boundary] <;> omega

/-- The first and second tag bits route to distinct continuation modes in a
finite positive number of steps, including all malformed low tags. -/
theorem dispatch (continuation : Nat → Bool → Row) (gap certificate stream : Nat) :
    ∃ t ≤ gap+4,
      (run (table continuation) ⟨2^gap*(2*certificate+1),2*stream,some 0⟩ t).state =
        some (5+mode certificate) := by
  by_cases hodd : certificate%2=1
  · have hbad : certificate%4 ≠ 0 := by omega
    refine ⟨gap+3,by omega,?_⟩
    have ht : gap+3=(gap+2)+1 := by omega
    rw [ht,run,reach_tag]
    simp [step,table,mode,hbad,Nat.testBit_zero,hodd]
  · have heven : certificate%2=0 := by omega
    refine ⟨gap+4,by omega,?_⟩
    have ht : gap+4=(gap+2)+2 := by omega
    rw [ht,Source284ScratchScanner.run_add,reach_tag]
    have hs : step (table continuation) ⟨boundary gap stream,certificate,some 3⟩ =
        ⟨2*boundary gap stream,certificate/2,some 4⟩ := by
      simp [step,table,bit,Nat.testBit_zero,heven]
    change (step (table continuation) (step (table continuation)
      ⟨boundary gap stream,certificate,some 3⟩)).state = _
    rw [hs]
    by_cases htag : certificate%4=0
    · have hhi : (certificate/2)%2=0 := by omega
      simp [step,table,mode,htag,Nat.testBit_zero,hhi]
    · have hhi : (certificate/2)%2=1 := by omega
      simp [step,table,mode,htag,Nat.testBit_zero,hhi]

/-- Valid tags reach exactly the original witness-packer entry layout. -/
theorem seek_valid (continuation : Nat → Bool → Row) (gap frame stream : Nat) :
    run (table continuation) ⟨2^gap*(2*(4*frame)+1),2*stream,some 0⟩ (gap+4) =
      ⟨Source284SingleCertificateSeek.inputSide gap stream,frame,some 5⟩ := by
  have ht : gap+4=(gap+2)+2 := by omega
  rw [ht,Source284ScratchScanner.run_add,reach_tag]
  have h3 (left : Nat) : step (table continuation) ⟨left,4*frame,some 3⟩ =
      ⟨2*left,2*frame,some 4⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.mul_mod] <;> omega
  have h4 (left : Nat) : step (table continuation) ⟨left,2*frame,some 4⟩ =
      ⟨2*left,frame,some 5⟩ := by simp [step,table,bit,Nat.testBit_zero]
  simp only [run,h3,h4,boundary,Source284SingleCertificateSeek.inputSide]
  congr 1 <;> ring

theorem seek_valid_then (continuation : Nat → Bool → Row) (gap frame stream fuel : Nat) :
    run (table continuation) ⟨2^gap*(2*(4*frame)+1),2*stream,some 0⟩ (gap+4+fuel) =
      shiftConfig 5 (run continuation
        ⟨Source284SingleCertificateSeek.inputSide gap stream,frame,some 0⟩ fuel) := by
  rw [Source284ScratchScanner.run_add,seek_valid]
  change run (table continuation) (shiftConfig 5
    ⟨Source284SingleCertificateSeek.inputSide gap stream,frame,some 0⟩) fuel = _
  exact relocated_run continuation _ fuel

/-- Invalid low tags are never accepted by the executable tagged decoder. -/
theorem bad_tag_decode (limit certificate : Nat) (h : mode certificate=1) :
    Source284TaggedWitnessCodec.decode limit certificate = none := by
  have hbad : certificate%4 ≠ 0 := by
    by_contra hc; simp [mode,hc] at h
  simp [Source284TaggedWitnessCodec.decode,hbad]

namespace Fixtures
def loop (_ : Nat) (b : Bool) : Row := ⟨b,false,some 0⟩
example : (run (table loop) ⟨2,0,some 0⟩ 5).state = some 5 := by decide +kernel
example : (run (table loop) ⟨6,0,some 0⟩ 4).state = some 6 := by decide +kernel
example : (run (table loop) ⟨10,0,some 0⟩ 5).state = some 6 := by decide +kernel
example : (run (table loop) ⟨14,0,some 0⟩ 4).state = some 6 := by decide +kernel
example : (run (table loop) ⟨18,0,some 0⟩ 5).state = some 5 := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284SingleTaggedDispatch
