import Shared.PNP.Record285.FramePrefixLoader

/-! Establish a one-cell left anchor on an actually blank cell and compose it
with the raw unary-frame scan and any valid finite continuation. This does not
encode the payload or prove the complete frame wrapper. -/
namespace Shared.PNP.Record285.FrameAnchorLoader
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (link shiftConfig shiftStatus run_shift)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.PNP.Record285.CanonicalInput

def anchorRows : Program :=
  [((false,false,1,0),(true,false,1,0)),
   ((true,true,2,0),(true,true,2,0))]

def program (p : Program) : Program := link anchorRows (FramePrefixLoader.program p) []

theorem program_valid (p : Program) (hp : valid p = true) : valid (program p) = true := by
  have hd : valid (link anchorRows FramePrefixLoader.dummy []) = true := by decide
  have hc := FramePrefixLoader.program_valid p hp
  have hn : 1 ≤ (FramePrefixLoader.program p).length :=
    Shared.Codes.FiniteProgramLink.valid_nonempty _ hc
  exact Shared.Codes.FiniteProgramRelink.valid_relink anchorRows FramePrefixLoader.dummy _ hd hc hn

/-- With a blank immediately left of the head, two actual transitions create
an anchor and return to the original head, retaining all other cells. -/
theorem anchor_start (p : Program) (left : List Bool) (b : Bool) (rest : List Bool)
    (hblank : left.head?.getD false = false) :
    run (program p) (0,tapeAt left (b::rest)) 2 =
      some (.inr (2,tapeAt (true::left.tail) (b::rest))) := by
  cases left with
  | nil => cases b <;> simp [run,advance,step,program,link,anchorRows,tapeAt,moveTape]
  | cons l ls =>
    have hl : l = false := by simpa using hblank
    subst l
    cases b <;> simp [run,advance,step,program,link,anchorRows,tapeAt,moveTape]

/-- The anchor and the scan compose with an arbitrary valid continuation;
the only changed cell is the formerly blank anchor immediately to the left. -/
theorem anchor_scan_then_continue (p : Program) (hp : valid p = true)
    (n fuel : Nat) (left rest : List Bool) (hblank : left.head?.getD false = false) :
    run (program p) (0,tapeAt left (List.replicate n true ++ false::rest)) (2+(n+1+fuel)) =
      shiftStatus 3 (run p
        (0,tapeAt (false::List.replicate n true ++ true::left.tail) rest) fuel) := by
  have ha : run (program p) (0,tapeAt left (List.replicate n true ++ false::rest)) 2 =
      some (.inr (2,tapeAt (true::left.tail) (List.replicate n true ++ false::rest))) := by
    cases n with
    | zero => simpa using anchor_start p left false rest hblank
    | succ n => simpa [List.replicate_succ] using
        anchor_start p left true (List.replicate n true ++ false::rest) hblank
  rw [run_continue _ _ _ _ _ ha]
  have hc := FramePrefixLoader.program_valid p hp
  have hlink := run_shift anchorRows (FramePrefixLoader.program p) [] hc
    (0,tapeAt (true::left.tail) (List.replicate n true ++ false::rest))
    (by have := Shared.Codes.FiniteProgramLink.valid_nonempty _ hc; omega) (n+1+fuel)
  have hscan := FramePrefixLoader.scan_then_continue p hp n fuel (true::left.tail) rest
  rw [hscan] at hlink
  have hcompose (s : Status) : shiftStatus 2 (shiftStatus 1 s) = shiftStatus 3 s := by
    cases s with
    | none => rfl
    | some v => cases v <;> simp [shiftStatus,shiftConfig] <;> omega
  change run (program p) (2,tapeAt (true::left.tail)
      (List.replicate n true ++ false::rest)) (n+1+fuel) =
    shiftStatus 2 (shiftStatus 1 (run p
      (0,tapeAt (false::List.replicate n true ++ true::left.tail) rest) fuel)) at hlink
  rw [hcompose] at hlink
  exact hlink

/-- Blank-start specialization retains the entire framed input and installs
only the explicit anchor before the continuation begins. -/
theorem anchor_scan_canonical (p : Program) (hp : valid p = true)
    (payload : List Bool) (fuel : Nat) :
    run (program p) (initial (canonical payload)) (2+(payload.length+1+fuel)) =
      shiftStatus 3 (run p
        (0,tapeAt (false::List.replicate payload.length true ++ [true]) payload) fuel) := by
  have h := anchor_scan_then_continue p hp payload.length fuel [] payload (by rfl)
  simpa [initial,canonical,tapeAt] using h

end Shared.PNP.Record285.FrameAnchorLoader
