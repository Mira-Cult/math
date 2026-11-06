import Shared.Beeping.NPcoNP.Source284FramedTerminal

/-! The finite verifier's reject state remains a nonaccepting sink inside
the actual joined serializer table. This is a building block for extending
certificate-dependent completion times to one common source clock. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace Shared.Beeping.NPcoNP.Source284FramedRejectSink

open Shared.Codes.FinitePrograms (Program Tape valid)
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig offset)
open Shared.Beeping.NPcoNP.Source284FramedEncoderTable

def frame (width : Nat) (p : Program) : Program :=
  Shared.Codes.FiniteProgramFrameUntagContinue.program width p

def innerSink (width : Nat) (p : Program) : Nat :=
  Source284FiniteRelativeRows.index (frame width p).length false

def outerOffset {width : Nat} (enc : Codec width) : Nat :=
  7+1+offset (word enc)+1+Source284DetectorExit.entry (rows enc).length

def sink {width : Nat} (enc : Codec width) (p : Program) : Nat := outerOffset enc+innerSink width p

/-- Every finite program's compiled row list has a self-looping reject row. -/
theorem program_sink_row (p : Program) (b : Bool) :
    Source284ListTables.table (Source284FiniteRelativeRows.rows p)
      (Source284FiniteRelativeRows.index p.length false) b =
      ⟨b,false,some (Source284FiniteRelativeRows.index p.length false)⟩ := by
  have hlt : Source284FiniteRelativeRows.index p.length false < 2*(p.length+1) := by
    simp [Source284FiniteRelativeRows.index,Source284CompileRecords.bit]
  rw [Source284FiniteRelativeRows.table_row _ _ hlt]
  have hi : Source284FiniteRelativeRows.index p.length false / 2 = p.length := by
    simp [Source284FiniteRelativeRows.index,Source284CompileRecords.bit]
  have hb : decide (Source284FiniteRelativeRows.index p.length false % 2 = 1) = false := by
    simp [Source284FiniteRelativeRows.index,Source284CompileRecords.bit]
  have hn : p[p.length]? = none := List.getElem?_eq_none (by omega)
  simp only [Source284FiniteRelativeRows.row,hi,hb,hn]

/-- This reject row is the one used by the framed verifier. -/
theorem base_sink_row (width : Nat) (p : Program) (b : Bool) :
    Source284ListTables.table (frameRows width p) (innerSink width p) b =
      ⟨b,false,some (innerSink width p)⟩ :=
  program_sink_row (frame width p) b

theorem base_sink_step (width : Nat) (p : Program) (left right : Nat) :
    (step (Source284ListTables.table (frameRows width p))
      ⟨left,right,some (innerSink width p)⟩).state = some (innerSink width p) := by
  simp [step,base_sink_row]

theorem sink_step {width : Nat} (enc : Codec width) (p : Program) (left right : Nat) :
    (step (table enc p) ⟨left,right,some (sink enc p)⟩).state = some (sink enc p) := by
  let c : Config := ⟨left,right,some (innerSink width p)⟩
  have h := congrArg Config.state (Source284FramedTerminal.serializer_relocated_step enc p c)
  have hc := base_sink_step width p left right
  repeat rw [Source284SourceRelocation.shiftConfig_add] at h
  change (step (table enc p) ⟨left,right,some (sink enc p)⟩).state =
    (shiftConfig (outerOffset enc) (step (Source284ListTables.table (frameRows width p)) c)).state at h
  change (step (table enc p) ⟨left,right,some (sink enc p)⟩).state =
    Option.map (fun q => outerOffset enc+q) (step (Source284ListTables.table (frameRows width p)) c).state at h
  rw [show (step (Source284ListTables.table (frameRows width p)) c).state =
    some (innerSink width p) from hc] at h
  exact h

theorem sink_run {width : Nat} (enc : Codec width) (p : Program) (c : Config)
    (hc : c.state = some (sink enc p)) (fuel : Nat) :
    (run (table enc p) c fuel).state = some (sink enc p) := by
  induction fuel with
  | zero => exact hc
  | succ fuel ih =>
    cases he : run (table enc p) c fuel with
    | mk left right state =>
      simp only [he] at ih
      subst state
      simpa [run,he] using sink_step enc p left right

theorem innerSink_lt (width : Nat) (p : Program) : innerSink width p < (frameRows width p).length := by
  have h (r : Program) : Source284FiniteRelativeRows.index r.length false <
      (Source284FiniteRelativeRows.rows r).length := by
    simp [Source284FiniteRelativeRows.rows_length,Source284FiniteRelativeRows.index,Source284CompileRecords.bit]
  exact h (frame width p)

theorem sink_lt {width : Nat} (enc : Codec width) (p : Program) : sink enc p < states enc p := by
  have h := innerSink_lt width p
  dsimp [sink,outerOffset,states,contStates]
  omega

/-- A false terminal row of the framed finite program enters the compiler's
reserved reject state, rather than merely being observed as nonzero. -/
theorem frame_reject_step (width : Nat) (p : Program) (q : Nat) (t : Tape) (rev : Bool)
    (hv : valid p = true) (hq : q < p.length)
    (hr : Shared.Codes.FinitePrograms.step p (q,t) = some (.inl false)) :
    (Source284Relative.step (Source284CompileRecords.compile (frame width p))
      (Source284FiniteTapeStep.represented t rev (Source284CompileRecords.codeState
        ((Shared.Codes.FiniteProgramFrameUntag.program width).length+2+q) rev))).state =
      Source284CompileRecords.rejectState (frame width p).length := by
  let qf := (Shared.Codes.FiniteProgramFrameUntag.program width).length+2+q
  have hframe : valid (frame width p) = true :=
    Shared.Codes.FiniteProgramFrameUntagContinue.program_valid width p hv
  have hqf : qf < (frame width p).length := by
    dsimp [qf,frame]
    rw [Shared.Codes.FiniteProgramFrameUntagContinue.program_length,
      Shared.Codes.FiniteProgramFrameUntag.program_length]
    omega
  have hstep := Source284FramedTerminal.frame_terminal_step width p q t false hv hq hr
  have hrun : Shared.Codes.FinitePrograms.run (frame width p) (qf,t) 1 = some (.inl false) := by
    simpa [frame,qf,Shared.Codes.FinitePrograms.run,Shared.Codes.FinitePrograms.advance] using hstep
  have hrel := Source284FiniteProgramRun.run_related (frame width p)
    (Source284FiniteProgramRun.closed_of_valid _ hframe) qf t rev hqf 1
  rw [hrun] at hrel
  cases hrel with
  | no _ hs => simpa [qf,Source284Relative.run] using hs

theorem toSource_state_reflect (c : Config) (q : Nat) (h : (toSource c).state = active q) :
    c.state = some q := by
  cases c with
  | mk left right state =>
    cases state with
    | none => simp [toSource,nextState,active] at h
    | some r =>
      have hr : r=q := by simp [toSource,nextState,active] at h; omega
      simpa [hr]

/-- At a false finite-program terminal row, the inner finite-row table
enters the precise reserved sink. -/
theorem base_terminal_reject (width : Nat) (p : Program) (q : Nat) (t : Tape) (rev : Bool)
    (hv : valid p = true) (hq : q < p.length)
    (hr : Shared.Codes.FinitePrograms.step p (q,t) = some (.inl false)) :
    let qf := (Shared.Codes.FiniteProgramFrameUntag.program width).length+2+q
    let i := Source284FiniteRelativeRows.index qf rev
    let rep := Source284FiniteTapeStep.represented t rev (Source284CompileRecords.codeState qf rev)
    (step (Source284ListTables.table (frameRows width p)) ⟨rep.left,rep.right,some i⟩).state =
      some (innerSink width p) := by
  dsimp only
  let qf := (Shared.Codes.FiniteProgramFrameUntag.program width).length+2+q
  let i := Source284FiniteRelativeRows.index qf rev
  let rep := Source284FiniteTapeStep.represented t rev (Source284CompileRecords.codeState qf rev)
  let c : Config := ⟨rep.left,rep.right,some i⟩
  have hqf : qf < (frame width p).length := by
    dsimp [qf,frame]
    rw [Shared.Codes.FiniteProgramFrameUntagContinue.program_length,
      Shared.Codes.FiniteProgramFrameUntag.program_length]
    omega
  have hi : i < (frameRows width p).length := by
    have hb := Source284CompileRecords.bit_lt rev
    have hlen : (frameRows width p).length = 2*((frame width p).length+1) :=
      Source284FiniteRelativeRows.rows_length (frame width p)
    rw [hlen]
    dsimp only [i,Source284FiniteRelativeRows.index]
    omega
  have hc : Valid (frameRows width p).length c := by
    intro j hj; simp [c] at hj; simpa [hj] using hi
  have hrep : toSource c = rep := by
    cases rev <;> simp [c,rep,qf,i,toSource,nextState,
      Source284FiniteRelativeRows.active_index,Source284FiniteTapeStep.represented,
      Source284CompileRecords.codeState,Source284FiniteRelativeRows.index,
      Source284CompileRecords.bit,active] <;> omega
  have hbase := step_toSource (frameRows width p).length
    (Source284ListTables.table (frameRows width p)) 1 c hc
  change Source284Relative.step (encode (Source284FiniteRelativeRows.rows (frame width p)).length
    (Source284ListTables.table (Source284FiniteRelativeRows.rows (frame width p))) 1) (toSource c) = _ at hbase
  rw [Source284FiniteRelativeRun.encode_eq_compile,hrep] at hbase
  have hreject := frame_reject_step width p q t rev hv hq hr
  have hstate := congrArg Source284Relative.Config.state hbase
  rw [hreject] at hstate
  have hs : Source284CompileRecords.rejectState (frame width p).length = active (innerSink width p) := by
    change Source284CompileRecords.codeState (frame width p).length false =
      active (Source284FiniteRelativeRows.index (frame width p).length false)
    exact (Source284FiniteRelativeRows.active_index (frame width p).length false).symm
  rw [hs] at hstate
  exact toSource_state_reflect _ _ hstate.symm

/-- The actual encoded serializer continuation enters its precise reject
sink after the false terminal transition. -/
theorem serializer_terminal_reject {width : Nat} (enc : Codec width) (p : Program)
    (q : Nat) (t : Tape) (rev : Bool) (hv : valid p = true) (hq : q < p.length)
    (hr : Shared.Codes.FinitePrograms.step p (q,t) = some (.inl false)) :
    (Source284Relative.step (encode (states enc p) (table enc p) 1)
      (Source284FramedEncoder.target enc p (q,t) rev)).state = active (sink enc p) := by
  let qf := (Shared.Codes.FiniteProgramFrameUntag.program width).length+2+q
  let i := Source284FiniteRelativeRows.index qf rev
  let rep := Source284FiniteTapeStep.represented t rev (Source284CompileRecords.codeState qf rev)
  let c : Config := ⟨rep.left,rep.right,some i⟩
  let nested := shiftConfig 7 (shiftConfig 1 (shiftConfig (offset (word enc))
    (shiftConfig 1 (shiftConfig (Source284DetectorExit.entry (rows enc).length) c))))
  have hi : i < (frameRows width p).length := by
    have hb := Source284CompileRecords.bit_lt rev
    have hqf : qf < (frame width p).length := by
      dsimp [qf,frame]
      rw [Shared.Codes.FiniteProgramFrameUntagContinue.program_length,
        Shared.Codes.FiniteProgramFrameUntag.program_length]
      omega
    have hlen : (frameRows width p).length = 2*((frame width p).length+1) :=
      Source284FiniteRelativeRows.rows_length (frame width p)
    rw [hlen]
    dsimp only [i,Source284FiniteRelativeRows.index]
    omega
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
  have hinner : (step (Source284ListTables.table (frameRows width p)) c).state = some (innerSink width p) :=
    base_terminal_reject width p q t rev hv hq hr
  have houter := step_toSource (states enc p) (table enc p) 1 nested hnested
  rw [ht,houter]
  dsimp only [nested]
  rw [Source284FramedTerminal.serializer_relocated_step]
  repeat rw [Source284SourceRelocation.shiftConfig_add]
  change (toSource (shiftConfig (outerOffset enc)
    (step (Source284ListTables.table (frameRows width p)) c))).state = _
  simp only [toSource,shiftConfig,hinner,Option.map_some,nextState,sink]

end Shared.Beeping.NPcoNP.Source284FramedRejectSink
