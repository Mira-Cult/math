import Shared.PNP.Record285.PythonStraight
import Shared.Beeping.Events

/-! Executable control-flow model for the typed source listing. This is a
partial semantics on initialized nonnegative integers, not a proof that
CPython's parser or all Python semantics coincide with it. A fault or return
is an administrative sink in this model only; no physical-machine progress
or event equivalence is claimed here. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControl
open Shared.Beeping
open Shared.PNP.Record285.PythonSyntax
open Shared.PNP.Record285.PythonStraight

def lineIndent : Line → Option Nat
  | .function _ _ => some 0
  | .blank => none
  | .while_ i _ | .if_ i _ | .else_ i | .assign i _ _ |
    .assignMany i _ _ | .aug i _ _ _ | .call i _ | .return_ i _ |
    .break_ i => some i

/-- Find the first following nonblank line no deeper than the given header.
The explicit fuel bounds the scan even on malformed listings. -/
def seekAux (code : Array Line) (level : Nat) : Nat → Nat → Nat
  | _, 0 => code.size
  | pc, fuel+1 =>
      match code[pc]? with
      | none => code.size
      | some line =>
          match lineIndent line with
          | some i => if i ≤ level then pc else seekAux code level (pc+1) fuel
          | none => seekAux code level (pc+1) fuel

def seek (code : Array Line) (pc level : Nat) : Nat :=
  seekAux code level pc code.size

structure Loop where
  head : Nat
  exit : Nat
  deriving DecidableEq, Repr

structure Config where
  pc : Nat
  store : Store
  loops : List Loop

inductive Status where
  | live : Config → Status
  | returned : Nat → Status
  | fault : Status

/-- On a dedent past a loop body, return to its header. Pop each completed
loop frame before rechecking enclosing frames. -/
def settle : Nat → List Loop → Nat × List Loop
  | pc, [] => (pc,[])
  | pc, loop::loops =>
      if loop.exit ≤ pc then settle loop.head loops else (pc,loop::loops)

def advance (pc : Nat) (s : Store) (loops : List Loop) : Status :=
  .live ⟨pc,s,loops⟩

def jumpFalse (code : Array Line) (pc level : Nat) : Nat :=
  let target := seek code (pc+1) level
  match code[target]? with
  | some (.else_ i) => if i=level then target+1 else target
  | _ => target

/-- One line step, labelled by the `beep` call. Unsupported operations,
underflow, missing lines and `break` outside a loop produce an explicit fault. -/
def step (code : Array Line) : Status → Status × Bool
  | .returned n => (.returned n,false)
  | .fault => (.fault,false)
  | .live c =>
      let settled := settle c.pc c.loops
      let pc := settled.1
      let loops := settled.2
      match code[pc]? with
      | none => (.fault,false)
      | some line =>
          match line with
          | .while_ level guard =>
              match eval c.store guard with
              | none => (.fault,false)
              | some value =>
                  let exit := seek code (pc+1) level
                  if value=0 then (advance exit c.store loops,false)
                  else (advance (pc+1) c.store (⟨pc,exit⟩::loops),false)
          | .if_ level guard =>
              match eval c.store guard with
              | none => (.fault,false)
              | some value =>
                  if value=0 then (advance (jumpFalse code pc level) c.store loops,false)
                  else (advance (pc+1) c.store loops,false)
          | .else_ level => (advance (seek code (pc+1) level) c.store loops,false)
          | .break_ _ =>
              match loops with
              | [] => (.fault,false)
              | loop::outer => (advance loop.exit c.store outer,false)
          | .call _ name =>
              if name="beep" then (advance (pc+1) c.store loops,true)
              else (.fault,false)
          | .return_ _ e =>
              match eval c.store e with
              | none => (.fault,false)
              | some value => (.returned value,false)
          | .assign _ _ _ | .assignMany _ _ _ | .aug _ _ _ _ =>
              match simple line c.store with
              | none => (.fault,false)
              | some store => (advance (pc+1) store loops,false)
          | .blank => (advance (pc+1) c.store loops,false)
          | .function _ _ => (.fault,false)

def code : Array Line := sourceLines.toArray

def mainSystem : EventSystem Status :=
  ⟨.live ⟨27,fun _ => 0,[]⟩,step code⟩

/-- The exact typed listing begins `main` at line index 26 and executes its
initial assignment at 27, then its outer loop header, then a marked beep. -/
theorem main_entry_rows :
    code[26]? = some (.function "main" []) ∧
    code[27]? = some (.assignMany 4 ["program","exponent"] [.num 0,.num 1]) ∧
    code[28]? = some (.while_ 4 .truth) ∧ code[29]? = some (.call 8 "beep") := by decide

theorem main_initial_events :
    ¬ mainSystem.BeepAt 0 ∧ ¬ mainSystem.BeepAt 1 ∧ mainSystem.BeepAt 2 := by
  unfold EventSystem.BeepAt
  decide

end Shared.PNP.Record285.PythonControl
