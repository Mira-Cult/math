import Shared.PNP.Record285.FrameBufferBlankStart
import Shared.Codes.FiniteProgramTwoExit

/-! A paid continuation from the blank-start tagged-payload extractor. -/
namespace Shared.PNP.Record285.FrameBufferHandoff
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.PNP.Record285.CanonicalInput
open Shared.PNP.Record285.FrameBufferBlankStart

def source : Program := FrameAnchorLoader.program FrameBufferLoader.program

theorem source_valid : valid source = true :=
  FrameAnchorLoader.program_valid _ FrameBufferLoader.program_valid

theorem source_length : source.length = 63 := by decide

theorem source_stop (tape : Tape) : step source (18,tape) = some (.inl false) := by
  have hr : source[18]? = some ((false,true,3,1),(true,true,3,1)) := by decide
  cases h : tape.2.1 <;> simp [step,hr,h]

def program (continuation : Program) : Program :=
  Shared.Codes.FiniteProgramTwoExit.program source continuation 18 18

theorem program_valid (p : Program) (hp : valid p = true) : valid (program p) = true :=
  Shared.Codes.FiniteProgramTwoExit.program_valid source p 18 18 source_valid hp
    (by rw [source_length]; decide) (by rw [source_length]; decide)

/-- The two-transition branch-and-return handoff may append a physically blank
cell to a finite list representation, but never changes the represented tape. -/
theorem handoff (p : Program) (tape : Tape) :
    ∃ tape', run (program p) (18,tape) 2 = some (.inr (65,tape')) ∧ TapeRel tape tape' := by
  have hr := Shared.Codes.FiniteProgramTwoExit.second_row source p 18 18 (by rw [source_length]; decide)
  have hb := Shared.Codes.FiniteProgramTwoExit.second_bridge source p 18 18
  rw [source_length] at hr hb
  rcases tape with ⟨left,head,right⟩
  cases right with
  | nil =>
    refine ⟨(left,head,[false]),?_,?_⟩
    · cases head <;> simp [program,run,advance,step,hr,hb,
        Shared.Codes.FiniteProgramExtendAdvance.branch,Shared.Codes.FiniteProgramExtendAdvance.bridge,moveTape]
    · simpa [tapeAt] using pad_right_one left [head]
  | cons next rest =>
    refine ⟨(left,head,next::rest),?_,rfl⟩
    cases head <;> cases next <;> simp [program,run,advance,step,hr,hb,
      Shared.Codes.FiniteProgramExtendAdvance.branch,Shared.Codes.FiniteProgramExtendAdvance.bridge,moveTape]

/-- The blank-start extractor plus paid continuation handoff preserve the
entire tagged tape, not just the parsed payload value. -/
theorem blank_start_handoff (p : Program) (payload : List Bool) :
    ∃ tape, run (program p) (initial (canonical payload)) (elapsed payload+2) =
        some (.inr (65,tape)) ∧ TapeRel tape (expectedTape payload) := by
  obtain ⟨tape,hload,htape⟩ := blank_start_extraction payload
  have hfirst := Shared.Codes.FiniteProgramTwoExit.first_entry source p 18 18
    (initial (canonical payload)) (18,tape) (elapsed payload)
    source_valid (by rw [source_length]; simp [initial]) source_stop source_stop hload
  change run (program p) (initial (canonical payload)) (elapsed payload) = _ at hfirst
  obtain ⟨tape',hh,ht⟩ := handoff p tape
  refine ⟨tape',?_,ht.symm.trans htape⟩
  rw [run_continue _ _ _ _ _ hfirst]
  exact hh

theorem shift_status_related (offset : Nat) (a b : Status) (h : StatusRel a b) :
    StatusRel (Shared.Codes.FiniteProgramLink.shiftStatus offset a)
      (Shared.Codes.FiniteProgramLink.shiftStatus offset b) := by
  cases a with
  | none => cases b <;> simp [StatusRel,Shared.Codes.FiniteProgramLink.shiftStatus] at h ⊢
  | some av => cases av with
    | inl x => cases b with
      | none => simp [StatusRel] at h
      | some bv => cases bv with
        | inl y => simpa [StatusRel,Shared.Codes.FiniteProgramLink.shiftStatus] using h
        | inr y => simp [StatusRel] at h
    | inr x => cases b with
      | none => simp [StatusRel] at h
      | some bv => cases bv with
        | inl y => simp [StatusRel] at h
        | inr y =>
          simp only [StatusRel] at h
          simp [StatusRel,Shared.Codes.FiniteProgramLink.shiftStatus,
            Shared.Codes.FiniteProgramLink.shiftConfig,h.1,h.2]

/-- Every finite run of an arbitrary valid continuation is reproduced from
the extracted tagged tape, with exact program-state relocation and complete
head-relative tape equivalence, after the paid handoff. -/
theorem blank_start_then_continue (p : Program) (hp : valid p = true)
    (payload : List Bool) (fuel : Nat) :
    StatusRel (run (program p) (initial (canonical payload)) (elapsed payload+2+fuel))
      (Shared.Codes.FiniteProgramLink.shiftStatus 65 (run p (0,expectedTape payload) fuel)) := by
  obtain ⟨tape,hload,htape⟩ := blank_start_handoff p payload
  rw [run_continue _ _ _ _ _ hload]
  have hq : (0 : Nat) < p.length := Shared.Codes.FiniteProgramLink.valid_nonempty p hp
  have hs := Shared.Codes.FiniteProgramLink.run_shift
    (Shared.Codes.FiniteProgramTwoExit.pre source 18 18) p [] hp (0,tape) hq fuel
  have hlen : (Shared.Codes.FiniteProgramTwoExit.pre source 18 18).length = 65 := by
    rw [Shared.Codes.FiniteProgramTwoExit.pre_length,source_length]
  rw [hlen] at hs
  change run (program p) (65,tape) fuel =
    Shared.Codes.FiniteProgramLink.shiftStatus 65 (run p (0,tape) fuel) at hs
  rw [hs]
  exact shift_status_related 65 _ _ (run_related p (0,tape) (0,expectedTape payload) rfl htape fuel)

theorem handoff_bound (payload : List Bool) :
    elapsed payload+2 ≤ payload.length*(12*payload.length+35)+12 := by
  have h := elapsed_bound payload
  omega

end Shared.PNP.Record285.FrameBufferHandoff
