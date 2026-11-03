import Shared.Codes.FiniteProgramRelink
import Shared.PNP.Record285.CanonicalInput

/-! A finite-table first phase for the exact `1^n 0 payload` source frame.
It scans through the unary delimiter and hands off the untouched payload,
including any finite high suffix, to an arbitrary relocated continuation. -/
namespace Shared.PNP.Record285.FramePrefixLoader
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (link shiftPair shiftConfig shiftStatus run_shift)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.PNP.Record285.CanonicalInput

def scanRows : Program := [((false,true,1,0),(true,true,0,0))]

def program (continuation : Program) : Program := link scanRows continuation []

def dummy : Program := [((false,true,0,1),(true,true,0,1))]

theorem program_valid (p : Program) (hp : valid p = true) : valid (program p) = true := by
  have hd : valid (link scanRows dummy []) = true := by decide
  have hn : 1 ≤ p.length := Shared.Codes.FiniteProgramLink.valid_nonempty p hp
  exact Shared.Codes.FiniteProgramRelink.valid_relink scanRows dummy p hd hp hn

theorem scan_one (p : Program) (left rest : List Bool) :
    run (program p) (0,tapeAt left (true::rest)) 1 =
      some (.inr (0,tapeAt (true::left) rest)) := by
  cases rest <;> simp [run,advance,step,program,link,scanRows,tapeAt,moveTape]

theorem scan_delimiter (p : Program) (left rest : List Bool) :
    run (program p) (0,tapeAt left (false::rest)) 1 =
      some (.inr (1,tapeAt (false::left) rest)) := by
  cases rest <;> simp [run,advance,step,program,link,scanRows,tapeAt,moveTape]

/-- Exactly one step per unary one, then one delimiter step. Every cell in
`rest` and on the untouched left is retained as actual tape data. -/
theorem scan (p : Program) (n : Nat) (left rest : List Bool) :
    run (program p) (0,tapeAt left (List.replicate n true ++ false::rest)) (n+1) =
      some (.inr (1,tapeAt (false::List.replicate n true ++ left) rest)) := by
  induction n generalizing left with
  | zero => simpa using scan_delimiter p left rest
  | succ n ih =>
    have hfirst := scan_one p left (List.replicate n true ++ false::rest)
    have he : n+1+1 = 1+(n+1) := by omega
    simp only [List.replicate_succ,List.cons_append]
    rw [he,run_continue _ _ _ _ _ hfirst,ih]
    have hrep : List.replicate n true ++ true::left = true::(List.replicate n true ++ left) := by
      have h : List.replicate n true ++ [true] = true::List.replicate n true := by
        rw [← List.replicate_succ', List.replicate_succ]
      simpa [List.append_assoc] using congrArg (fun xs => xs ++ left) h
    simp only [List.cons_append]
    rw [hrep]

/-- The delimiter scan and every step of an arbitrary valid continuation
compose with no unchecked tape or head projection. -/
theorem scan_then_continue (p : Program) (hp : valid p = true)
    (n fuel : Nat) (left rest : List Bool) :
    run (program p) (0,tapeAt left (List.replicate n true ++ false::rest)) (n+1+fuel) =
      shiftStatus 1 (run p (0,tapeAt (false::List.replicate n true ++ left) rest) fuel) := by
  rw [run_continue _ _ _ _ _ (scan p n left rest)]
  have hs := run_shift scanRows p [] hp (0,tapeAt (false::List.replicate n true ++ left) rest)
    (by have := Shared.Codes.FiniteProgramLink.valid_nonempty p hp; omega) fuel
  simpa [program,scanRows,shiftConfig] using hs

/-- Blank-start specialization for the exact canonical frame, including the
empty payload and trailing false payload bits. -/
theorem scan_canonical (p : Program) (payload : List Bool) :
    run (program p) (initial (canonical payload)) (payload.length+1) =
      some (.inr (1,tapeAt (false::List.replicate payload.length true) payload)) := by
  have h := scan p payload.length [] payload
  simpa [initial,canonical,tapeAt] using h

end Shared.PNP.Record285.FramePrefixLoader
