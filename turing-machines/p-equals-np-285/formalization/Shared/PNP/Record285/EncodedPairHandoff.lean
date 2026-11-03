import Shared.PNP.Record285.EncodedPairStart

/-! Paid continuation from either exit of the genuine blank-start tagged loop.
The output is still a tagged intermediate representation. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.EncodedPairHandoff
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (shiftConfig shiftStatus run_shift)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.Codes.FiniteProgramTwoExit

def source : Program := FrameBufferHandoff.program (FrameBufferSeek.program (FramePairProbe.program EncodedPairStart.program))

theorem source_valid : valid source = true :=
  FrameBufferHandoff.program_valid _ (FrameBufferSeek.program_valid _
    (FramePairProbe.program_valid _ EncodedPairStart.program_valid EncodedPairStart.program_length))

theorem source_length : source.length = 178 := by decide

theorem stop_first (tape : Tape) : step source (174,tape) = some (.inl false) := by
  have hr : source[174]? = some ((false,true,172,1),(true,true,172,1)) := by decide
  cases h : tape.2.1 <;> simp [step,hr,h]

theorem stop_second (tape : Tape) : step source (177,tape) = some (.inl false) := by
  have hr : source[177]? = some ((false,true,74,1),(true,true,74,1)) := by decide
  cases h : tape.2.1 <;> simp [step,hr,h]

def program (p : Program) : Program := Shared.Codes.FiniteProgramTwoExit.program source p 174 177

theorem program_valid (p : Program) (hp : valid p = true) : valid (program p) = true :=
  Shared.Codes.FiniteProgramTwoExit.program_valid source p 174 177 source_valid hp
    (by rw [source_length]; decide) (by rw [source_length]; decide)

/-- Two paid moves preserve the complete tagged tape from either physical exit. -/
theorem blank_start_handoff (p : Program) (payload : List Bool) :
    ∃ tape, run (program p) (initial (CanonicalInput.canonical payload))
      (EncodedPairStart.duration payload+2) = some (.inr (180,tape)) ∧
      TapeRel tape (EncodedPairStart.outputTape payload) := by
  obtain ⟨tape,hr,ht⟩ := EncodedPairStart.blank_start_output payload
  have hr' := first_entry source p 174 177 (initial (CanonicalInput.canonical payload))
    (EncodedPairStart.exitState payload,tape) (EncodedPairStart.duration payload)
    source_valid (by rw [source_length]; simp [initial]) stop_first stop_second hr
  change run (program p) (initial (CanonicalInput.canonical payload)) _ = _ at hr'
  let L := [false,false]
  let R := Shared.Codes.FiniteProgramBitShuttle.tagged (EncodedPairLoop.emitted false payload) ++ [false,false,false]
  have hshape : EncodedPairStart.outputTape payload = tapeAt L (true::false::R) := by
    rfl
  have hrel : TapeRel tape (tapeAt L (true::false::R)) := ht.trans (by rw [hshape])
  have hrun := run_related (program p) (EncodedPairStart.exitState payload,tape)
    (EncodedPairStart.exitState payload,tapeAt L (true::false::R)) rfl hrel 2
  have hstep : run (program p) (EncodedPairStart.exitState payload,tapeAt L (true::false::R)) 2 =
      some (.inr (180,tapeAt L (true::false::R))) := by
    cases payload with
    | nil =>
      simpa [program,EncodedPairStart.exitState,pre_length,source_length] using
        handoff_second source p 174 177 (by rw [source_length]; decide) true false L R
    | cons bit rest =>
      simpa [program,EncodedPairStart.exitState,pre_length,source_length] using
        handoff_first source p 174 177 (by rw [source_length]; decide) (by decide) true false L R
  rw [hstep] at hrun
  cases hactual : run (program p) (EncodedPairStart.exitState payload,tape) 2 with
  | none => rw [hactual] at hrun; exact False.elim hrun
  | some v => cases v with
    | inl b => rw [hactual] at hrun; exact False.elim hrun
    | inr d =>
      rw [hactual] at hrun
      have hd : d.1 = 180 ∧ TapeRel d.2 (tapeAt L (true::false::R)) := hrun
      refine ⟨d.2,?_,hd.2.trans (by rw [hshape])⟩
      rw [run_continue _ _ _ _ _ hr',hactual]
      cases d with | mk q t => simp only at hd; rw [hd.1]

/-- Every finite continuation run is simulated after a bounded initialization,
including exact state relocation and the whole tape, even on timeout. -/
theorem blank_start_then_continue (p : Program) (hp : valid p = true)
    (payload : List Bool) (fuel : Nat) :
    StatusRel (run (program p) (initial (CanonicalInput.canonical payload))
        (EncodedPairStart.duration payload+2+fuel))
      (shiftStatus 180 (run p (0,EncodedPairStart.outputTape payload) fuel)) := by
  obtain ⟨tape,hload,htape⟩ := blank_start_handoff p payload
  rw [run_continue _ _ _ _ _ hload]
  have hq : (0 : Nat) < p.length := Shared.Codes.FiniteProgramLink.valid_nonempty p hp
  have hs := run_shift (pre source 174 177) p [] hp (0,tape) hq fuel
  have hlen : (pre source 174 177).length = 180 := by rw [pre_length,source_length]
  rw [hlen] at hs
  change run (program p) (180,tape) fuel = shiftStatus 180 (run p (0,tape) fuel) at hs
  rw [hs]
  exact FrameBufferHandoff.shift_status_related 180 _ _
    (run_related p (0,tape) (0,EncodedPairStart.outputTape payload) rfl htape fuel)

theorem handoff_bound (payload : List Bool) :
    EncodedPairStart.duration payload+2 ≤ payload.length*(108*payload.length+137)+22 := by
  have h := EncodedPairStart.duration_bound payload
  omega

end Shared.PNP.Record285.EncodedPairHandoff
