import Shared.PNP.Record285.EncodedPairHandoff
import Shared.Codes.FiniteProgramSingleUntag
import Shared.ComplexityBridge.TM2Diagonal

/-! The genuine blank-start frame is converted to the reverse-oriented
canonical encoding of its payload. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PayloadEncoding
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.Codes.FiniteProgramLink (shiftStatus shiftConfig)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.Codes.FiniteProgramUntag (cost)

def words (payload : List Bool) : List Bool := EncodedPairLoop.emitted false payload

theorem words_eq (payload : List Bool) :
    words payload = payload.flatMap (fun b => [false,b,true]) := by
  induction payload with
  | nil => rfl
  | cons b bs ih => simp [words,EncodedPairLoop.emitted] at ih ⊢; exact ih

theorem words_reverse (payload : List Bool) :
    (words payload).reverse = BitstringEncoding.bitEncode payload.reverse := by
  rw [← Shared.ComplexityBridge.TM2Diagonal.encoded_eq,words_eq,List.reverse_flatMap]
  simp [Shared.ComplexityBridge.TM2Diagonal.encoded,Function.comp_def]

theorem reflected_initial_append_blank (xs : List Bool) :
    TapeRel (Shared.Codes.FiniteProgramMirror.tape (initial (xs ++ [false])).2)
      (Shared.Codes.FiniteProgramMirror.tape (initial xs).2) := by
  cases xs with
  | nil => rfl
  | cons head tail =>
    have h : Turing.ListBlank.mk (tail ++ [false]) = Turing.ListBlank.mk tail := by
      apply Quotient.sound
      exact Or.inr ⟨1,by simp⟩
    unfold TapeRel Shared.Codes.FiniteProgramMirror.tape initial
    change (⟨head,Turing.ListBlank.mk (tail ++ [false]),Turing.ListBlank.mk []⟩ : Turing.Tape Bool) =
      ⟨head,Turing.ListBlank.mk tail,Turing.ListBlank.mk []⟩
    rw [h]

/-- After untagging, the whole tape is a reflected canonical input for the
reversed payload. The reversed order will be accounted for by the canonical
polynomial-time source predicate. -/
theorem raw_reflected (payload : List Bool) :
    TapeRel (Shared.Codes.FiniteProgramSingleUntag.rawTape (words payload))
      (Shared.Codes.FiniteProgramMirror.tape
        (initial (BitstringEncoding.bitEncode payload.reverse)).2) := by
  have h := Shared.Codes.FiniteProgramSingleUntag.rawTape_reflected (words payload)
  rw [words_reverse] at h
  exact h.trans (reflected_initial_append_blank _)

/-- The head-side extra blanks are physically equivalent to the exact input
expected by the existing sentinel eraser and untagger. -/
theorem output_related (payload : List Bool) :
    TapeRel (EncodedPairStart.outputTape payload)
      (tapeAt [] (true::false::Shared.Codes.FiniteProgramBitShuttle.tagged (words payload) ++ [false,false,false])) := by
  have h := FrameBufferBlankStart.pad_left []
    (true::false::Shared.Codes.FiniteProgramBitShuttle.tagged (words payload) ++ [false,false,false]) 2
  simpa [TapeRel,EncodedPairStart.outputTape,Shared.Codes.FiniteProgramTaggedLoop.canonical,words] using h.symm

def program : Program := EncodedPairHandoff.program Shared.Codes.FiniteProgramSingleUntag.convert

theorem program_valid : valid program = true :=
  EncodedPairHandoff.program_valid _ Shared.Codes.FiniteProgramSingleUntag.convert_valid

def duration (payload : List Bool) : Nat :=
  EncodedPairStart.duration payload+2+(2+cost (words payload))

/-- The real encoded-triple loop and real untagger compose from blank start,
with exact state and a full-tape relation. -/
theorem blank_start_payload (payload : List Bool) :
    ∃ tape, run program (initial (CanonicalInput.canonical payload)) (duration payload) =
      some (.inr (194,tape)) ∧
      TapeRel tape (Shared.Codes.FiniteProgramSingleUntag.rawTape (words payload)) := by
  let conv := Shared.Codes.FiniteProgramSingleUntag.convert
  let t := tapeAt [] (true::false::Shared.Codes.FiniteProgramBitShuttle.tagged (words payload) ++ [false,false,false])
  let out := Shared.Codes.FiniteProgramSingleUntag.rawTape (words payload)
  have hp := EncodedPairHandoff.blank_start_then_continue conv
    Shared.Codes.FiniteProgramSingleUntag.convert_valid payload (2+cost (words payload))
  have hr := run_related conv (0,EncodedPairStart.outputTape payload) (0,t) rfl
    (output_related payload) (2+cost (words payload))
  have hc := Shared.Codes.FiniteProgramSingleUntag.convert_run (words payload)
  change run conv (0,t) (2+cost (words payload)) = some (.inr (14,out)) at hc
  rw [hc] at hr
  have hshift := FrameBufferHandoff.shift_status_related 180 _ _ hr
  have hall := FramePairProbe.status_trans _ _ _ hp hshift
  change StatusRel (run program (initial (CanonicalInput.canonical payload)) (duration payload))
    (some (.inr (194,out))) at hall
  cases hrun : run program (initial (CanonicalInput.canonical payload)) (duration payload) with
  | none => rw [hrun] at hall; exact False.elim hall
  | some v => cases v with
    | inl b => rw [hrun] at hall; exact False.elim hall
    | inr d =>
      rw [hrun] at hall
      have hd : d.1 = 194 ∧ TapeRel d.2 out := hall
      refine ⟨d.2,?_,hd.2⟩
      cases d with | mk q t => simp only at hd; rw [hd.1]

theorem words_length (payload : List Bool) : (words payload).length = 3*payload.length := by
  rw [words_eq]
  induction payload with
  | nil => rfl
  | cons b bs ih => simp [List.flatMap_cons,ih]; omega

/-- Preparation, sentinel removal and all untagging steps have a uniform
quadratic bound. -/
theorem duration_bound (payload : List Bool) :
    duration payload ≤ payload.length*(288*payload.length+200)+28 := by
  have hp := EncodedPairHandoff.handoff_bound payload
  have hu := Shared.Codes.FiniteProgramUntag.cost_bound (words payload)
  rw [words_length] at hu
  unfold duration
  nlinarith

end Shared.PNP.Record285.PayloadEncoding
