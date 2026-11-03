import Shared.PNP.Record285.ControlInvariantData

/-! Kernel checks of the reverse mask for preserving paths to control parents. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.ControlInvariant
open Shared.Beeping.Machines
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.DispatcherInvariant (forward)
open Shared.PNP.Record285.ControlInvariantData
open Shared.PNP.Record285.Grammar (decTerminal halfTerminal)

def backward (q : Fin 285) (d : Nat) : Bool := (backwardData[q.val]?.getD 0).testBit d

def edgeCheck (q : Fin 285) (b : Bool) : Bool :=
  let row := NumericTables.target.table.row q b
  if forward q && decide (row.write = b ∧ row.move = .right ∧ row.beep = false) then
    forward row.next && (List.range 5).all (fun d =>
      if backward row.next d then
        match detectorNext d b with
        | none => false
        | some d' => backward q d'
      else true)
  else true

def stateCheck (q : Fin 285) : Bool := edgeCheck q false && edgeCheck q true

def chunkCheck (start count : Nat) : Bool :=
  (List.range' start count).all fun i =>
    if h : i < 285 then stateCheck ⟨i,h⟩ else false

theorem chunk0 : chunkCheck 0 16 = true := by decide
theorem chunk1 : chunkCheck 16 16 = true := by decide
theorem chunk2 : chunkCheck 32 16 = true := by decide
theorem chunk3 : chunkCheck 48 16 = true := by decide
theorem chunk4 : chunkCheck 64 16 = true := by decide
theorem chunk5 : chunkCheck 80 16 = true := by decide
theorem chunk6 : chunkCheck 96 16 = true := by decide
theorem chunk7 : chunkCheck 112 16 = true := by decide
theorem chunk8 : chunkCheck 128 16 = true := by decide
theorem chunk9 : chunkCheck 144 16 = true := by decide
theorem chunk10 : chunkCheck 160 16 = true := by decide
theorem chunk11 : chunkCheck 176 16 = true := by decide
theorem chunk12 : chunkCheck 192 16 = true := by decide
theorem chunk13 : chunkCheck 208 16 = true := by decide
theorem chunk14 : chunkCheck 224 16 = true := by decide
theorem chunk15 : chunkCheck 240 16 = true := by decide
theorem chunk16 : chunkCheck 256 16 = true := by decide
theorem chunk17 : chunkCheck 272 13 = true := by decide

def controlSeed (n : Nat) : Bool :=
  match (Grammar.fastNodes[n]?).map (fun p => p.2) with
  | some (Grammar.Edge.brk _) | some (Grammar.Edge.cont _) => backward (Grammar.state n) 0
  | _ => true

def seedChunk (start count : Nat) : Bool := (List.range' start count).all controlSeed

theorem seed0 : seedChunk 0 16 = true := by decide
theorem seed1 : seedChunk 16 16 = true := by decide
theorem seed2 : seedChunk 32 16 = true := by decide
theorem seed3 : seedChunk 48 16 = true := by decide
theorem seed4 : seedChunk 64 16 = true := by decide
theorem seed5 : seedChunk 80 16 = true := by decide
theorem seed6 : seedChunk 96 16 = true := by decide
theorem seed7 : seedChunk 112 16 = true := by decide
theorem seed8 : seedChunk 128 16 = true := by decide
theorem seed9 : seedChunk 144 16 = true := by decide
theorem seed10 : seedChunk 160 3 = true := by decide

end Shared.PNP.Record285.ControlInvariant
