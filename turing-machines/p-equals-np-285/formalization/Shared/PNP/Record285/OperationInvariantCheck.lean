import Shared.PNP.Record285.OperationInvariantData

/-! Kernel checks of the reverse mask for preserving paths to operation terminals. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.OperationInvariant
open Shared.Beeping.Machines
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.DispatcherInvariant (forward)
open Shared.PNP.Record285.OperationInvariantData
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

def decSeed (i : Nat) : Bool := backward (decTerminal i) 0
def incSeed (i : Nat) : Bool := backward (IncrementPreparation.terminal i) 0
def halfSeed (i : Nat) : Bool := backward (halfTerminal i) 0

theorem dec_seed_all : (List.range 15).all decSeed = true := by decide
theorem inc_seed_all : (List.range 15).all incSeed = true := by decide
theorem half_seed_all : (List.range 4).all halfSeed = true := by decide
theorem beep_seed : backward ⟨121,by decide⟩ 0 = true := by decide
theorem root_mask : backwardData[284]?.getD 0 = 3 := by decide

end Shared.PNP.Record285.OperationInvariant
