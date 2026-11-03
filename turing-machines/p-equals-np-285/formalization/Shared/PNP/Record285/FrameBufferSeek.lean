import Shared.PNP.Record285.FrameBufferHandoff
import Shared.Codes.FiniteProgramRelink

/-! Move from the extracted tagged tape to the buffer separator, then hand
its complete tape to a relocated finite continuation. -/
namespace Shared.PNP.Record285.FrameBufferSeek
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (link shiftStatus shiftConfig run_shift)
open Shared.Codes.FiniteProgramTapeEquiv (StatusRel)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.PNP.Record285.CanonicalInput

def scanRows : Program := [((false,false,0,0),(true,false,1,0))]
def dummy : Program := [((false,true,0,1),(true,true,0,1))]
def program (p : Program) : Program := link scanRows p []

theorem program_valid (p : Program) (hp : valid p = true) : valid (program p) = true := by
  have hd : valid (link scanRows dummy []) = true := by decide
  have hn : 1 ≤ p.length := Shared.Codes.FiniteProgramLink.valid_nonempty p hp
  exact Shared.Codes.FiniteProgramRelink.valid_relink scanRows dummy p hd hp hn

theorem zero_step (p : Program) (left right : List Bool) :
    run (program p) (0,tapeAt (false::left) (false::right)) 1 =
      some (.inr (0,tapeAt left (false::false::right))) := by
  simp [run,advance,step,program,link,scanRows,tapeAt,moveTape]

theorem scan_zeros (p : Program) (n : Nat) (left right : List Bool) :
    run (program p) (0,tapeAt (List.replicate n false ++ left) (false::right)) n =
      some (.inr (0,tapeAt left (List.replicate (n+1) false ++ right))) := by
  induction n generalizing right with
  | zero => simp
  | succ n ih =>
    have hfirst := zero_step p (List.replicate n false ++ left) right
    have hn : n+1 = 1+n := by omega
    simp only [List.replicate_succ,List.cons_append]
    rw [hn,run_continue _ _ _ _ _ hfirst,ih]
    congr 3
    simp only [List.replicate_succ,List.cons_append]
    have hrep : List.replicate n false ++ false::right = false::(List.replicate n false ++ right) := by
      have h : List.replicate n false ++ [false] = false::List.replicate n false := by
        rw [← List.replicate_succ',List.replicate_succ]
      simpa [List.append_assoc] using congrArg (fun xs => xs ++ right) h
    rw [hrep]

/-- The head finishes on the blank separator immediately to the left of the
anchor. The tagged buffer and all right-side cells remain explicit. -/
theorem seek (p : Program) (n : Nat) (left right : List Bool) :
    run (program p) (0,tapeAt (List.replicate n false ++ true::false::left) (false::right)) (n+2) =
      some (.inr (1,tapeAt left (false::true::List.replicate (n+1) false ++ right))) := by
  have hs := scan_zeros p n (true::false::left) right
  have hend : run (program p)
      (0,tapeAt (true::false::left) (List.replicate (n+1) false ++ right)) 2 =
      some (.inr (1,tapeAt left (false::true::List.replicate (n+1) false ++ right))) := by
    simp only [List.replicate_succ,List.cons_append]
    simp [run,advance,step,program,link,scanRows,tapeAt,moveTape]
  rw [run_continue _ _ _ _ _ hs]
  exact hend

theorem seek_then_continue (p : Program) (hp : valid p = true) (n fuel : Nat)
    (left right : List Bool) :
    run (program p) (0,tapeAt (List.replicate n false ++ true::false::left) (false::right)) (n+2+fuel) =
      shiftStatus 1 (run p (0,tapeAt left (false::true::List.replicate (n+1) false ++ right)) fuel) := by
  rw [run_continue _ _ _ _ _ (seek p n left right)]
  have h := run_shift scanRows p [] hp
    (0,tapeAt left (false::true::List.replicate (n+1) false ++ right))
    (by have := Shared.Codes.FiniteProgramLink.valid_nonempty p hp; omega) fuel
  simpa [program,scanRows,shiftConfig] using h

/-- The actual blank-start extractor and the head-positioning phase compose
with every finite run of an arbitrary valid tagged-buffer continuation. -/
theorem blank_start_then_continue (p : Program) (hp : valid p = true)
    (payload : List Bool) (fuel : Nat) :
    StatusRel (run (FrameBufferHandoff.program (program p)) (initial (canonical payload))
        (FrameBufferBlankStart.elapsed payload+2+(2*payload.length+2+fuel)))
      (shiftStatus 66 (run p
        (0,tapeAt (FrameBufferLoader.tagged payload)
          (false::true::List.replicate (2*payload.length+1) false ++ [false])) fuel)) := by
  have hvalid := program_valid p hp
  have h := FrameBufferHandoff.blank_start_then_continue (program p) hvalid payload (2*payload.length+2+fuel)
  have hs := seek_then_continue p hp (2*payload.length) fuel (FrameBufferLoader.tagged payload) [false]
  change run (program p) (0,FrameBufferBlankStart.expectedTape payload)
      (2*payload.length+2+fuel) = _ at hs
  rw [hs] at h
  have hcompose (s : Status) : shiftStatus 65 (shiftStatus 1 s) = shiftStatus 66 s := by
    cases s with
    | none => rfl
    | some v => cases v <;> simp [shiftStatus,shiftConfig] <;> omega
  rw [hcompose] at h
  exact h

theorem seek_bound (payload : List Bool) :
    FrameBufferBlankStart.elapsed payload+2+(2*payload.length+2) ≤
      payload.length*(12*payload.length+37)+14 := by
  have h := FrameBufferBlankStart.elapsed_bound payload
  nlinarith

end Shared.PNP.Record285.FrameBufferSeek
