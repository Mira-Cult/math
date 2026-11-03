import Shared.PNP.Record285.ControlInvariant
import Shared.PNP.Record285.GrammarLeafDispatch

/-! Every literal control leaf has a detector-safe preserving prefix. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.ControlInvariant
open Shared.Beeping.Machines
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.Grammar
attribute [local irreducible] fastNodes

theorem seed_interval (start count : Nat) (h : seedChunk start count = true)
    (n : Nat) (hlo : start ≤ n) (hhi : n < start+count) : controlSeed n = true := by
  apply List.all_eq_true.mp h n
  simp only [List.mem_range']
  refine ⟨n-start,?_,?_⟩ <;> omega

theorem checked_seed (n : Nat) (hn : n < 163) : controlSeed n = true := by
  by_cases h0 : n < 16
  · exact seed_interval 0 16 seed0 n (by omega) (by omega)
  by_cases h1 : n < 32
  · exact seed_interval 16 16 seed1 n (by omega) (by omega)
  by_cases h2 : n < 48
  · exact seed_interval 32 16 seed2 n (by omega) (by omega)
  by_cases h3 : n < 64
  · exact seed_interval 48 16 seed3 n (by omega) (by omega)
  by_cases h4 : n < 80
  · exact seed_interval 64 16 seed4 n (by omega) (by omega)
  by_cases h5 : n < 96
  · exact seed_interval 80 16 seed5 n (by omega) (by omega)
  by_cases h6 : n < 112
  · exact seed_interval 96 16 seed6 n (by omega) (by omega)
  by_cases h7 : n < 128
  · exact seed_interval 112 16 seed7 n (by omega) (by omega)
  by_cases h8 : n < 144
  · exact seed_interval 128 16 seed8 n (by omega) (by omega)
  by_cases h9 : n < 160
  · exact seed_interval 144 16 seed9 n (by omega) (by omega)
  exact seed_interval 160 3 seed10 n (by omega) (by omega)

theorem continue_parent_seed (parent i : Nat) (h : nodeEdge parent true = some (.cont i)) :
    backward (state parent) 0 = true := by
  have he : (fastNodes[parent]?).map (fun p => p.2) = some (.cont i) := by
    simpa only [nodeEdge,nodes_fast,if_true] using h
  have hb := mapped_lookup_bound fastNodes (fun p => p.2) parent (.cont i) he
  have hn : parent < 163 := by simpa only [nodes_size] using hb
  have hc := checked_seed parent hn
  unfold controlSeed at hc
  rw [he] at hc
  exact hc

theorem break_parent_seed (parent i : Nat) (h : nodeEdge parent true = some (.brk i)) :
    backward (state parent) 0 = true := by
  have he : (fastNodes[parent]?).map (fun p => p.2) = some (.brk i) := by
    simpa only [nodeEdge,nodes_fast,if_true] using h
  have hb := mapped_lookup_bound fastNodes (fun p => p.2) parent (.brk i) he
  have hn : parent < 163 := by simpa only [nodes_size] using hb
  have hc := checked_seed parent hn
  unfold controlSeed at hc
  rw [he] at hc
  exact hc

theorem continue_prefix_safe (code : List Bool) (i : Nat)
    (hwalk : walk 162 code = some (.cont i)) :
    ∃ pre parent row, code = pre++[true] ∧ route treeRoot pre = some (state parent) ∧
      nodeEdge parent true = some (.cont i) ∧ expected (.cont i) true = some row ∧
      Record285.machine.table.row (state parent) true = row ∧
      detectorRun 0 (scanWord pre) = some 0 := by
  obtain ⟨pre,bit,parent,row,hcode,hroute,hedge,hexpected,hrow⟩ := root_final_edge code (.cont i) hwalk
  cases bit with
  | false => simp [expected] at hexpected
  | true =>
    refine ⟨pre,parent,row,hcode,hroute,hedge,hexpected,hrow,?_⟩
    exact route_is_safe pre (state parent) (continue_parent_seed parent i hedge) hroute

theorem break_prefix_safe (code : List Bool) (i : Nat)
    (hwalk : walk 162 code = some (.brk i)) :
    ∃ pre parent row, code = pre++[true] ∧ route treeRoot pre = some (state parent) ∧
      nodeEdge parent true = some (.brk i) ∧ expected (.brk i) true = some row ∧
      Record285.machine.table.row (state parent) true = row ∧
      detectorRun 0 (scanWord pre) = some 0 := by
  obtain ⟨pre,bit,parent,row,hcode,hroute,hedge,hexpected,hrow⟩ := root_final_edge code (.brk i) hwalk
  cases bit with
  | false => simp [expected] at hexpected
  | true =>
    refine ⟨pre,parent,row,hcode,hroute,hedge,hexpected,hrow,?_⟩
    exact route_is_safe pre (state parent) (break_parent_seed parent i hedge) hroute

end Shared.PNP.Record285.ControlInvariant
