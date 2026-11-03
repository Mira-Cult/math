import Shared.PNP.Record285.FrameBufferLoop
import Shared.Codes.FiniteProgramTaggedLoop

/-! Connect the full tagged-buffer extraction to a wholly blank initial tape.
Finite list representations may contain additional explicit blank cells. -/
namespace Shared.PNP.Record285.FrameBufferBlankStart
open Turing
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.PNP.Record285.FrameBufferLoader
open Shared.PNP.Record285.FrameBufferLoop
open Shared.PNP.Record285.CanonicalInput

theorem pad_left (left right : List Bool) (n : Nat) :
    TapeRel (tapeAt left right) (tapeAt (left ++ List.replicate n false) right) := by
  unfold TapeRel
  change (⟨right.head?.getD false,Turing.ListBlank.mk left,Turing.ListBlank.mk right.tail⟩ : Turing.Tape Bool) =
    ⟨right.head?.getD false,Turing.ListBlank.mk (left ++ List.replicate n false),Turing.ListBlank.mk right.tail⟩
  have hl : Turing.ListBlank.mk left = Turing.ListBlank.mk (left ++ List.replicate n false) := by
    apply Quotient.sound
    exact Or.inl ⟨n,rfl⟩
  rw [hl]

theorem pad_right_one (left right : List Bool) :
    TapeRel (tapeAt left right) (tapeAt left (right ++ [false])) := by
  cases right with
  | nil => rfl
  | cons b bs =>
    simpa using Shared.Codes.FiniteProgramTaggedLoop.tapeAt_append_blank left bs b

theorem padded_left (payload : List Bool) :
    workLeft 0 [] payload [] =
      (false::List.replicate payload.length true ++ [true]) ++
        List.replicate (2*payload.length+1) false := by
  simp [workLeft,tagged,List.replicate_succ,List.append_assoc]

/-- The actual post-prefix tape and the finite padded workspace denote exactly
the same infinite blank tape, including payloads ending with zero bits. -/
theorem initial_tape_related (payload : List Bool) :
    TapeRel (tapeAt (false::List.replicate payload.length true ++ [true]) payload)
      (tapeAt (workLeft 0 [] payload []) (payload ++ [false])) := by
  rw [padded_left]
  exact (pad_left _ _ _).trans (pad_right_one _ _)

def expectedTape (payload : List Bool) : Tape :=
  tapeAt (List.replicate (2*payload.length) false ++ true::false::tagged payload) [false,false]

def elapsed (payload : List Bool) : Nat :=
  2+(payload.length+1+cost 0 0 payload.length)

/-- The actual blank-start machine reaches the full tagged payload layout,
up to the standard quotient by finite blank padding, with the head and every
tape cell accounted for. This is an auxiliary loader, not the record machine. -/
theorem blank_start_extraction (payload : List Bool) :
    ∃ tape, run (FrameAnchorLoader.program program) (initial (canonical payload)) (elapsed payload) =
        some (.inr (18,tape)) ∧ TapeRel tape (expectedTape payload) := by
  let actual := tapeAt (false::List.replicate payload.length true ++ [true]) payload
  let padded := tapeAt (workLeft 0 [] payload []) (payload ++ [false])
  have hloop : run program (0,padded) (cost 0 0 payload.length) =
      some (.inr (15,expectedTape payload)) := by
    simpa [padded,expectedTape] using run_loop 0 [] payload [] false []
  have hrel := run_related program (0,actual) (0,padded) rfl (initial_tape_related payload)
    (cost 0 0 payload.length)
  rw [hloop] at hrel
  cases hr : run program (0,actual) (cost 0 0 payload.length) with
  | none => simp [hr,StatusRel] at hrel
  | some v =>
    cases v with
    | inl bit => simp [hr,StatusRel] at hrel
    | inr d =>
      have hd : d.1 = 15 ∧ TapeRel d.2 (expectedTape payload) := by simpa [hr,StatusRel] using hrel
      refine ⟨d.2,?_,hd.2⟩
      have ha := FrameAnchorLoader.anchor_scan_canonical program program_valid payload (cost 0 0 payload.length)
      change run (FrameAnchorLoader.program program) (initial (canonical payload)) (elapsed payload) =
        Shared.Codes.FiniteProgramLink.shiftStatus 3
          (run program (0,actual) (cost 0 0 payload.length)) at ha
      rw [hr] at ha
      simpa [Shared.Codes.FiniteProgramLink.shiftStatus,Shared.Codes.FiniteProgramLink.shiftConfig,hd.1] using ha

theorem elapsed_bound (payload : List Bool) :
    elapsed payload ≤ payload.length*(12*payload.length+35)+10 := by
  have h := cost_bound 0 0 payload.length
  simp only [elapsed,Nat.mul_zero,Nat.zero_add] at h ⊢
  nlinarith

end Shared.PNP.Record285.FrameBufferBlankStart
