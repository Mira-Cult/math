import Shared.PNP.Record285.EncodedPairLoop

/-! Connect the actual blank-start probe to the self-contained pair loop.
The remaining output is tagged; canonical serialization is still separate. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.EncodedPairStart
open Turing
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (link shiftConfig shiftStatus run_shift)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.Codes.FiniteProgramTaggedLoop (canonical)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def pre : Program :=
  [((false,true,3,0),(true,true,3,0)),
   ((false,true,3,0),(true,true,3,0)),
   ((false,true,103,0),(true,true,103,0)),
   ((false,false,4,0),(false,false,4,0))]
def terminal : Row × Row := ((false,true,0,1),(true,true,0,1))
def program : Program := link pre EncodedPairLoop.program [terminal]

theorem program_valid : valid program = true := by decide

theorem program_length : 3 ≤ program.length := by
  simp [program,link,pre]

def inputTape (payload : List Bool) : Tape :=
  tapeAt (FrameBufferLoader.tagged payload)
    (false::true::List.replicate (2*payload.length+1) false ++ [false])

def preparedTape (payload : List Bool) : Tape :=
  tapeAt (FrameBufferLoader.tagged payload)
    (false::false::List.replicate (2*payload.length+1) false ++ [false])

def idealTape (payload : List Bool) : Tape :=
  (canonical (FrameBufferLoader.tagged payload ++ [false,false]) false []).2

/-- Remove the temporary anchor and return the head to the separator. -/
theorem prepare (bit : Bool) (payload : List Bool) :
    run program ((if bit then 1 else 0),inputTape payload) 2 =
      some (.inr (4,preparedTape payload)) := by
  cases bit <;> simp [run,advance,step,program,link,pre,inputTape,preparedTape,tapeAt,moveTape]

/-- All padding beyond the finite payload is blank on the genuine input tape;
this equality refers to the entire infinite tape, not just a window. -/
theorem prepared_related (payload : List Bool) : TapeRel (preparedTape payload) (idealTape payload) := by
  have hl : Turing.ListBlank.mk (FrameBufferLoader.tagged payload) =
      Turing.ListBlank.mk (FrameBufferLoader.tagged payload ++ [false,false]) := by
    apply Quotient.sound
    exact Or.inl ⟨2,by simp⟩
  have hform : false::List.replicate (2*payload.length+1) false ++ [false] =
      List.replicate (2*payload.length+3) false := by
    have h1 : List.replicate (2*payload.length+2) false =
        false::List.replicate (2*payload.length+1) false := by
      conv_lhs => rw [show 2*payload.length+2 = (2*payload.length+1)+1 by omega,List.replicate_succ]
    have h2 : List.replicate (2*payload.length+3) false =
        List.replicate (2*payload.length+2) false ++ [false] := by
      conv_lhs => rw [show 2*payload.length+3 = (2*payload.length+2)+1 by omega,List.replicate_succ']
    rw [h2,h1]
  have hnil (n : Nat) : Turing.ListBlank.mk ([] : List Bool) = Turing.ListBlank.mk (List.replicate n false) := by
    apply Quotient.sound
    exact Or.inl ⟨n,by simp⟩
  unfold TapeRel preparedTape idealTape canonical tapeAt
  change (⟨false,Turing.ListBlank.mk (FrameBufferLoader.tagged payload),
      Turing.ListBlank.mk (false::List.replicate (2*payload.length+1) false ++ [false])⟩ : Turing.Tape Bool) =
    ⟨false,Turing.ListBlank.mk (FrameBufferLoader.tagged payload ++ [false,false]),
      Turing.ListBlank.mk [false,false,false,false]⟩
  rw [hl,hform,← hnil (2*payload.length+3)]
  have hfour := hnil 4
  simpa using hfour

def outputTape (payload : List Bool) : Tape :=
  (canonical [false,false] true (EncodedPairLoop.emitted false payload)).2

/-- After the probe's bit-specific entry, the real table erases the anchor,
runs the entire pair controller, and reaches its end row. -/
theorem prepare_then_loop (bit : Bool) (payload : List Bool) (hne : payload ≠ []) :
    ∃ tape, run program ((if bit then 1 else 0),inputTape payload)
        (2+EncodedPairLoop.loopCost false [] payload) = some (.inr (100,tape)) ∧
      TapeRel tape (outputTape payload) := by
  obtain ⟨expected,he,hq,ht⟩ := EncodedPairLoop.run_pairs false [] payload [] hne
    (0,idealTape payload) rfl (by rfl)
  have ht' : TapeRel expected.2 (outputTape payload) := by
    simpa [outputTape,EncodedPairLoop.loopOutput_eq] using ht
  have hrel := run_related EncodedPairLoop.program (0,preparedTape payload) (0,idealTape payload)
    rfl (prepared_related payload) (EncodedPairLoop.loopCost false [] payload)
  rw [he] at hrel
  cases hr : run EncodedPairLoop.program (0,preparedTape payload) (EncodedPairLoop.loopCost false [] payload) with
  | none => rw [hr] at hrel; exact False.elim hrel
  | some v => cases v with
    | inl out => rw [hr] at hrel; exact False.elim hrel
    | inr d =>
      rw [hr] at hrel
      have hd : d.1 = expected.1 ∧ TapeRel d.2 expected.2 := hrel
      have hs := run_shift pre EncodedPairLoop.program [terminal] EncodedPairLoop.program_valid
        (0,preparedTape payload)
        (Shared.Codes.FiniteProgramLink.valid_nonempty _ EncodedPairLoop.program_valid)
        (EncodedPairLoop.loopCost false [] payload)
      rw [hr] at hs
      refine ⟨d.2,?_,hd.2.trans ht'⟩
      rw [run_continue _ _ _ _ _ (prepare bit payload)]
      simpa [program,pre,shiftConfig,shiftStatus,hd.1,hq] using hs

/-- The previously verified blank-start extractor, bit probe and pair loop
compose to a complete tagged-output tape in finite physical time. -/
theorem blank_start_nonempty (bit : Bool) (rest : List Bool) :
    let payload := bit::rest
    ∃ tape, run (FrameBufferHandoff.program (FrameBufferSeek.program (FramePairProbe.program program)))
        (initial (CanonicalInput.canonical payload))
        (FrameBufferBlankStart.elapsed payload+2+(2*payload.length+2+
          (4+(2+EncodedPairLoop.loopCost false [] payload)))) = some (.inr (174,tape)) ∧
      TapeRel tape (outputTape payload) := by
  dsimp only
  let payload := bit::rest
  obtain ⟨tape,hr,ht⟩ := prepare_then_loop bit payload (by simp [payload])
  have hs := FramePairProbe.blank_start_nonempty program program_valid program_length bit rest
    (2+EncodedPairLoop.loopCost false [] payload)
  change StatusRel
    (run (FrameBufferHandoff.program (FrameBufferSeek.program (FramePairProbe.program program)))
      (initial (CanonicalInput.canonical payload))
      (FrameBufferBlankStart.elapsed payload+2+(2*payload.length+2+
        (4+(2+EncodedPairLoop.loopCost false [] payload)))))
    (shiftStatus 74 (run program ((if bit then 1 else 0),inputTape payload)
      (2+EncodedPairLoop.loopCost false [] payload))) at hs
  rw [hr] at hs
  simp only [shiftStatus,shiftConfig] at hs
  cases ha : run (FrameBufferHandoff.program (FrameBufferSeek.program (FramePairProbe.program program)))
      (initial (CanonicalInput.canonical payload))
      (FrameBufferBlankStart.elapsed payload+2+(2*payload.length+2+
        (4+(2+EncodedPairLoop.loopCost false [] payload)))) with
  | none => rw [ha] at hs; exact False.elim hs
  | some v => cases v with
    | inl out => rw [ha] at hs; exact False.elim hs
    | inr d =>
      rw [ha] at hs
      have hd : d.1 = 174 ∧ TapeRel d.2 tape := hs
      refine ⟨d.2,?_,hd.2.trans ht⟩
      cases d with | mk q t => simp only at hd; rw [hd.1]

theorem empty_prepare :
    run program (2,inputTape []) 1 =
      some (.inr (103,tapeAt [false] [true,false,false])) := by
  simp [run,advance,step,program,link,pre,terminal,inputTape,tapeAt,moveTape]

theorem empty_tape_related :
    TapeRel (tapeAt [false] [true,false,false]) (outputTape []) := by
  have hl : Turing.ListBlank.mk [false] = Turing.ListBlank.mk [false,false] := by
    apply Quotient.sound
    exact Or.inl ⟨1,by simp⟩
  have hr : Turing.ListBlank.mk [false,false] = Turing.ListBlank.mk [false,false,false,false] := by
    apply Quotient.sound
    exact Or.inl ⟨2,by simp⟩
  unfold TapeRel outputTape canonical tapeAt EncodedPairLoop.emitted
  simp only [Shared.Codes.FiniteProgramBitShuttle.tagged]
  change (⟨true,Turing.ListBlank.mk [false],Turing.ListBlank.mk [false,false]⟩ : Turing.Tape Bool) =
    ⟨true,Turing.ListBlank.mk [false,false],Turing.ListBlank.mk [false,false,false,false]⟩
  rw [hl,hr]

/-- The empty frame reaches the same whole-tape output convention. -/
theorem blank_start_empty :
    ∃ tape, run (FrameBufferHandoff.program (FrameBufferSeek.program (FramePairProbe.program program)))
        (initial (CanonicalInput.canonical []))
        (FrameBufferBlankStart.elapsed []+2+(2*0+2+(4+1))) = some (.inr (177,tape)) ∧
      TapeRel tape (outputTape []) := by
  have hs := FramePairProbe.blank_start_empty program program_valid program_length 1
  change StatusRel
    (run (FrameBufferHandoff.program (FrameBufferSeek.program (FramePairProbe.program program)))
      (initial (CanonicalInput.canonical []))
      (FrameBufferBlankStart.elapsed []+2+(2*0+2+(4+1))))
    (shiftStatus 74 (run program (2,inputTape []) 1)) at hs
  rw [empty_prepare] at hs
  simp only [shiftStatus,shiftConfig] at hs
  cases ha : run (FrameBufferHandoff.program (FrameBufferSeek.program (FramePairProbe.program program)))
      (initial (CanonicalInput.canonical []))
      (FrameBufferBlankStart.elapsed []+2+(2*0+2+(4+1))) with
  | none => rw [ha] at hs; exact False.elim hs
  | some v => cases v with
    | inl out => rw [ha] at hs; exact False.elim hs
    | inr d =>
      rw [ha] at hs
      have hd : d.1 = 177 ∧ TapeRel d.2 (tapeAt [false] [true,false,false]) := hs
      refine ⟨d.2,?_,hd.2.trans empty_tape_related⟩
      cases d with | mk q t => simp only at hd; rw [hd.1]

theorem total_bound (payload : List Bool) :
    FrameBufferBlankStart.elapsed payload+2+(2*payload.length+2+
      (4+(2+EncodedPairLoop.loopCost false [] payload))) ≤
      payload.length*(108*payload.length+137)+20 := by
  have hp := FramePairProbe.probe_bound payload
  have hl := EncodedPairLoop.loopCost_bound false [] payload
  simp only [List.length_nil,Nat.mul_zero,Nat.zero_add] at hl
  nlinarith

def exitState (payload : List Bool) : Nat := if payload.isEmpty then 177 else 174

def duration (payload : List Bool) : Nat :=
  FrameBufferBlankStart.elapsed payload+2+(2*payload.length+2+
    (4+(if payload.isEmpty then 1 else 2+EncodedPairLoop.loopCost false [] payload)))

/-- Both zero and nonzero inputs reach the same tagged whole-tape format. -/
theorem blank_start_output (payload : List Bool) :
    ∃ tape, run (FrameBufferHandoff.program (FrameBufferSeek.program (FramePairProbe.program program)))
        (initial (CanonicalInput.canonical payload)) (duration payload) =
          some (.inr (exitState payload,tape)) ∧ TapeRel tape (outputTape payload) := by
  cases payload with
  | nil => simpa [duration,exitState] using blank_start_empty
  | cons bit rest => simpa [duration,exitState] using blank_start_nonempty bit rest

theorem duration_bound (payload : List Bool) :
    duration payload ≤ payload.length*(108*payload.length+137)+20 := by
  cases payload with
  | nil =>
    have h := FramePairProbe.probe_bound ([] : List Bool)
    simp [duration] at h ⊢
    omega
  | cons bit rest => simpa [duration] using total_bound (bit::rest)

end Shared.PNP.Record285.EncodedPairStart
