import Shared.Beeping.NPcoNP.Source284VerifierPredecessor

/-! Terminal results inside the joined serializer's finite continuation.
This works at the inner framed-encoder table; the outer raw-loader relocation
and its runway hypotheses are addressed separately. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
namespace Shared.Beeping.NPcoNP.Source284FramedTerminal

open Shared.Codes.FinitePrograms (Program Tape valid)
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig offset)
open Shared.Beeping.NPcoNP.Source284FramedEncoderTable

/-- The existing serializer table preserves each continuation step after all
four paid control relocations. Acceptance remains unshifted. -/
theorem serializer_relocated_step {width : Nat} (enc : Codec width) (p : Program)
    (c : Config) :
    step (table enc p)
      (shiftConfig 7 (shiftConfig 1 (shiftConfig (offset (word enc))
        (shiftConfig 1 (shiftConfig (Source284DetectorExit.entry (rows enc).length) c))))) =
    shiftConfig 7 (shiftConfig 1 (shiftConfig (offset (word enc))
      (shiftConfig 1 (shiftConfig (Source284DetectorExit.entry (rows enc).length)
        (step (Source284ListTables.table (frameRows width p)) c))))) := by
  unfold table Source284TaggedMarkerSeed.table continuation
  rw [Source284JoinedPrefixScan.relocated_step,Source284EncoderMarkerSeed.relocated_step,
    Source284HardwireTable.relocated_step,Source284TaggedMarkerSeed.turn_relocated_step,
    Source284ClearExit.relocated_step]

/-- The finite untagging wrapper passes either terminal result from its
relocated verifier row in one step. -/
theorem frame_terminal_step (width : Nat) (p : Program) (q : Nat) (t : Tape) (b : Bool)
    (hv : valid p = true) (hq : q < p.length)
    (hr : Shared.Codes.FinitePrograms.step p (q,t) = some (.inl b)) :
    Shared.Codes.FinitePrograms.step (Shared.Codes.FiniteProgramFrameUntagContinue.program width p)
      (((Shared.Codes.FiniteProgramFrameUntag.program width).length+2+q),t) = some (.inl b) := by
  have h := Shared.Codes.FiniteProgramFrameUntagContinue.continuation_run width p hv (q,t) hq 1
  simpa [Shared.Codes.FinitePrograms.run,Shared.Codes.FinitePrograms.advance,
    Shared.Codes.FiniteProgramLink.shiftConfig,Shared.Codes.FiniteProgramLink.shiftStatus,hr] using h

/-- The standalone compiled frame/untag table exposes the verifier result
after exactly its terminal transition. -/
theorem frame_compiled_terminal (width : Nat) (p : Program) (q : Nat) (t : Tape) (rev b : Bool)
    (hv : valid p = true) (hq : q < p.length)
    (hr : Shared.Codes.FinitePrograms.step p (q,t) = some (.inl b)) :
    ((Source284Relative.step
      (Source284CompileRecords.compile (Shared.Codes.FiniteProgramFrameUntagContinue.program width p))
      (Source284FiniteTapeStep.represented t rev (Source284CompileRecords.codeState
        ((Shared.Codes.FiniteProgramFrameUntag.program width).length+2+q) rev))).state == 0) = b := by
  let frame := Shared.Codes.FiniteProgramFrameUntagContinue.program width p
  have hframe : valid frame = true := Shared.Codes.FiniteProgramFrameUntagContinue.program_valid width p hv
  have hqf : (Shared.Codes.FiniteProgramFrameUntag.program width).length+2+q < frame.length := by
    dsimp [frame]
    rw [Shared.Codes.FiniteProgramFrameUntagContinue.program_length,
      Shared.Codes.FiniteProgramFrameUntag.program_length]
    omega
  exact Source284VerifierPredecessor.compiled_result_step frame _ t rev b hframe hqf
    (frame_terminal_step width p q t b hv hq hr)

theorem shifted_acceptance (d : Nat) (c : Config) :
    ((toSource (shiftConfig d c)).state == 0) = ((toSource c).state == 0) := by
  rcases c with ⟨l,r,s⟩
  cases s <;> simp [toSource,shiftConfig,nextState,active]

/-- The terminal result survives all serializer-table relocations. The source
step here belongs to the inner framed table, before the outer loader offset. -/
theorem serializer_terminal_step {width : Nat} (enc : Codec width) (p : Program)
    (q : Nat) (t : Tape) (rev b : Bool) (hv : valid p = true) (hq : q < p.length)
    (hr : Shared.Codes.FinitePrograms.step p (q,t) = some (.inl b)) :
    ((Source284Relative.step (encode (states enc p) (table enc p) 1)
      (Source284FramedEncoder.target enc p (q,t) rev)).state == 0) = b := by
  let frame := Shared.Codes.FiniteProgramFrameUntagContinue.program width p
  let qf := (Shared.Codes.FiniteProgramFrameUntag.program width).length+2+q
  let i := Source284FiniteRelativeRows.index qf rev
  let rep := Source284FiniteTapeStep.represented t rev (Source284CompileRecords.codeState qf rev)
  let c : Config := ⟨rep.left,rep.right,some i⟩
  let nested := shiftConfig 7 (shiftConfig 1 (shiftConfig (offset (word enc))
    (shiftConfig 1 (shiftConfig (Source284DetectorExit.entry (rows enc).length) c))))
  have hi : i < (frameRows width p).length := by
    have hb := Source284CompileRecords.bit_lt rev
    have hqf : qf < frame.length := by
      dsimp [qf,frame]
      rw [Shared.Codes.FiniteProgramFrameUntagContinue.program_length,
        Shared.Codes.FiniteProgramFrameUntag.program_length]
      omega
    have hlen : (frameRows width p).length = 2*(frame.length+1) :=
      Source284FiniteRelativeRows.rows_length frame
    rw [hlen]
    dsimp only [i,Source284FiniteRelativeRows.index]
    omega
  have hc : Valid (frameRows width p).length c := by
    intro j hj
    simp [c] at hj
    simpa [hj] using hi
  have hnested : Valid (states enc p) nested := by
    intro j hj
    simp only [nested,shiftConfig,c,Option.map_some,Option.some.injEq] at hj
    subst j
    dsimp [states,contStates]
    omega
  have hrep : toSource c = rep := by
    cases rev <;> simp [c,rep,qf,i,toSource,nextState,
      Source284FiniteRelativeRows.active_index,Source284FiniteTapeStep.represented,
      Source284CompileRecords.codeState,Source284FiniteRelativeRows.index,
      Source284CompileRecords.bit,active] <;> omega
  have ht : Source284FramedEncoder.target enc p (q,t) rev = toSource nested := by
    change Source284SourceRelocation.lift (7+Source284FramedSerialize.seedCost enc)
      (Source284SourceRelocation.lift (Source284DetectorExit.entry (rows enc).length) rep) = _
    rw [← hrep,Source284SourceRelocation.lift_toSource,Source284SourceRelocation.lift_toSource]
    dsimp only [nested]
    simp only [Source284SourceRelocation.shiftConfig_add,Source284FramedSerialize.seedCost]
    apply congrArg (fun n => toSource (shiftConfig n c))
    change 7+(1+offset (word enc)+1)+Source284DetectorExit.entry (rows enc).length = _
    omega
  have hbase := step_toSource (frameRows width p).length
    (Source284ListTables.table (frameRows width p)) 1 c hc
  change Source284Relative.step (encode (Source284FiniteRelativeRows.rows frame).length
    (Source284ListTables.table (Source284FiniteRelativeRows.rows frame)) 1) (toSource c) = _ at hbase
  rw [Source284FiniteRelativeRun.encode_eq_compile,hrep] at hbase
  have houter := step_toSource (states enc p) (table enc p) 1 nested hnested
  rw [ht,houter]
  dsimp only [nested]
  rw [serializer_relocated_step]
  rw [shifted_acceptance 7,shifted_acceptance 1,shifted_acceptance (offset (word enc)),
    shifted_acceptance 1,shifted_acceptance (Source284DetectorExit.entry (rows enc).length)]
  rw [← hbase]
  exact frame_compiled_terminal width p q t rev b hv hq hr

end Shared.Beeping.NPcoNP.Source284FramedTerminal
