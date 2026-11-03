import Shared.PNP.Record285.GrammarFastData

/-! A small finite checker of every producer grammar edge against the literal
numeric table, including the non-preserving break and continue operations. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.Grammar
open Shared.Beeping.Machines
open Shared.PNP.Record285.GenericDispatch

def state (n : Nat) : Fin 285 :=
  ⟨(stateMap[n]?.getD 0) % 285, Nat.mod_lt _ (by decide)⟩

def decTerminal (i : Nat) : Fin 285 :=
  ⟨((IncrementPreparation.terminal i).val-1) % 285, Nat.mod_lt _ (by decide)⟩

def halfTerminal (i : Nat) : Fin 285 := ⟨(105+i) % 285, Nat.mod_lt _ (by decide)⟩

def breakTerminal : Nat → Option (Fin 285)
  | 0 => some ⟨1,by decide⟩ | 1 => some ⟨117,by decide⟩
  | 2 => some ⟨118,by decide⟩ | _ => none

def continueTerminal : Nat → Option (Fin 285)
  | 1 => some ⟨119,by decide⟩ | 2 => some ⟨120,by decide⟩ | _ => none

/-- Exact expected physical row for each grammar-edge kind. -/
def expected : Edge → Bool → Option (Row 285)
  | .node j,b => if j < fastNodes.size then some ⟨b,.right,state j,false⟩ else none
  | .inc i,b => if i < 15 then some ⟨b,.right,IncrementPreparation.terminal i,false⟩ else none
  | .dec i,b => if i < 15 then some ⟨b,.right,decTerminal i,false⟩ else none
  | .half i,b => if i < 4 then some ⟨b,.right,halfTerminal i,false⟩ else none
  | .beep,b => some ⟨b,.right,⟨121,by decide⟩,false⟩
  | .brk i,b => if b then (breakTerminal i).map (fun q => ⟨false,.left,q,false⟩) else none
  | .cont i,b => if b then (continueTerminal i).map (fun q => ⟨false,.left,q,false⟩) else none

def checkEdge (q : Fin 285) (b : Bool) (edge : Edge) : Bool :=
  match expected edge b with
  | none => false
  | some row => decide (NumericTables.target.table.row q b = row)

def nodeCheck (n : Nat) : Bool :=
  match fastNodes[n]? with
  | none => false
  | some pair => checkEdge (state n) false pair.1 && checkEdge (state n) true pair.2

def chunkCheck (start count : Nat) : Bool :=
  (List.range' start count).all nodeCheck

theorem nodes_size : fastNodes.size = 163 := by decide
theorem stateMap_size : stateMap.size = 163 := by decide
theorem stateMap_bounds : stateMap.toList.all (fun q => q < 285) = true := by decide
theorem root_state : state 162 = treeRoot := by decide

theorem chunk0 : chunkCheck 0 8 = true := by decide
theorem chunk1 : chunkCheck 8 8 = true := by decide
theorem chunk2 : chunkCheck 16 8 = true := by decide
theorem chunk3 : chunkCheck 24 8 = true := by decide
theorem chunk4 : chunkCheck 32 8 = true := by decide
theorem chunk5 : chunkCheck 40 8 = true := by decide
theorem chunk6 : chunkCheck 48 8 = true := by decide
theorem chunk7 : chunkCheck 56 8 = true := by decide
theorem chunk8 : chunkCheck 64 8 = true := by decide
theorem chunk9 : chunkCheck 72 8 = true := by decide
theorem chunk10 : chunkCheck 80 8 = true := by decide
theorem chunk11 : chunkCheck 88 8 = true := by decide
theorem chunk12 : chunkCheck 96 8 = true := by decide
theorem chunk13 : chunkCheck 104 8 = true := by decide
theorem chunk14 : chunkCheck 112 8 = true := by decide
theorem chunk15 : chunkCheck 120 8 = true := by decide
theorem chunk16 : chunkCheck 128 8 = true := by decide
theorem chunk17 : chunkCheck 136 8 = true := by decide
theorem chunk18 : chunkCheck 144 8 = true := by decide
theorem chunk19 : chunkCheck 152 8 = true := by decide
theorem chunk20 : chunkCheck 160 3 = true := by decide

end Shared.PNP.Record285.Grammar
