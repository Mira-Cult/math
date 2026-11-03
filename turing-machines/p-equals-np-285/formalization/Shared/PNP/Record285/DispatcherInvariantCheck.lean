import Shared.PNP.Record285.DispatcherInvariantData

/-! Finite checked forward reachability and reverse detector-safety closure. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.DispatcherInvariant
open Shared.Beeping.Machines
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.DispatcherInvariantData

def forward (q : Fin 285) : Bool := forwardData[q.val]?.getD false

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

theorem forward_root : forward treeRoot = true := by decide

def seedCheck (i : Nat) : Bool := backward (IncrementPreparation.terminal i) 0

theorem seed_all : (List.range 15).all seedCheck = true := by decide

theorem root_mask : backwardData[284]?.getD 0 = 3 := by decide

end Shared.PNP.Record285.DispatcherInvariant
