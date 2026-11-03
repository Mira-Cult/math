import Shared.PNP.Record285.ControlBreakRankCheck

/-! Checked lower bounds on zero bits along literal preserving routes. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.ControlBreakRank
open Shared.Beeping.Machines
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.DispatcherInvariant (forward forward_root detector_append)
open Shared.PNP.Record285.ControlBreakRankData
open Shared.PNP.Record285.Grammar
attribute [local irreducible] fastNodes

 theorem chunk_sound (start count : Nat) (hcheck : chunkCheck start count = true)
    (q : Fin 285) (hmem : q.val ∈ List.range' start count) : stateCheck q = true := by
  have hc := List.all_eq_true.mp hcheck q.val hmem
  simpa only [dif_pos q.isLt] using hc

theorem chunk_interval (start count : Nat) (hcheck : chunkCheck start count = true)
    (q : Fin 285) (hlo : start ≤ q.val) (hhi : q.val < start+count) : stateCheck q = true := by
  apply chunk_sound start count hcheck q ?_
  simp only [List.mem_range']
  refine ⟨q.val-start, ?_, ?_⟩ <;> omega

theorem checked_state (q : Fin 285) : stateCheck q = true := by
  have hq := q.isLt
  by_cases h0 : q.val < 16
  · exact chunk_interval 0 16 chunk0 q (by omega) (by omega)
  by_cases h1 : q.val < 32
  · exact chunk_interval 16 16 chunk1 q (by omega) (by omega)
  by_cases h2 : q.val < 48
  · exact chunk_interval 32 16 chunk2 q (by omega) (by omega)
  by_cases h3 : q.val < 64
  · exact chunk_interval 48 16 chunk3 q (by omega) (by omega)
  by_cases h4 : q.val < 80
  · exact chunk_interval 64 16 chunk4 q (by omega) (by omega)
  by_cases h5 : q.val < 96
  · exact chunk_interval 80 16 chunk5 q (by omega) (by omega)
  by_cases h6 : q.val < 112
  · exact chunk_interval 96 16 chunk6 q (by omega) (by omega)
  by_cases h7 : q.val < 128
  · exact chunk_interval 112 16 chunk7 q (by omega) (by omega)
  by_cases h8 : q.val < 144
  · exact chunk_interval 128 16 chunk8 q (by omega) (by omega)
  by_cases h9 : q.val < 160
  · exact chunk_interval 144 16 chunk9 q (by omega) (by omega)
  by_cases h10 : q.val < 176
  · exact chunk_interval 160 16 chunk10 q (by omega) (by omega)
  by_cases h11 : q.val < 192
  · exact chunk_interval 176 16 chunk11 q (by omega) (by omega)
  by_cases h12 : q.val < 208
  · exact chunk_interval 192 16 chunk12 q (by omega) (by omega)
  by_cases h13 : q.val < 224
  · exact chunk_interval 208 16 chunk13 q (by omega) (by omega)
  by_cases h14 : q.val < 240
  · exact chunk_interval 224 16 chunk14 q (by omega) (by omega)
  by_cases h15 : q.val < 256
  · exact chunk_interval 240 16 chunk15 q (by omega) (by omega)
  by_cases h16 : q.val < 272
  · exact chunk_interval 256 16 chunk16 q (by omega) (by omega)
  exact chunk_interval 272 13 chunk17 q (by omega) (by omega)

theorem checked_edge (q : Fin 285) (b : Bool) : edgeCheck q b = true := by
  have h := checked_state q
  simp only [stateCheck,Bool.and_eq_true] at h
  cases b with
  | false => exact h.1
  | true => exact h.2

/-- Each literal preserving transition can increase the checked lower bound
by at most the zero bit actually consumed. -/
theorem edge_rank (q : Fin 285) (b : Bool) (hfwd : forward q = true)
    (hrow : (NumericTables.target.table.row q b).write = b ∧
      (NumericTables.target.table.row q b).move = .right ∧
      (NumericTables.target.table.row q b).beep = false) :
    rank (NumericTables.target.table.row q b).next ≤ rank q + if b then 0 else 1 := by
  have hc := checked_edge q b
  have he : (forward q && decide ((NumericTables.target.table.row q b).write = b ∧
      (NumericTables.target.table.row q b).move = .right ∧
      (NumericTables.target.table.row q b).beep = false)) = true := by simp [hfwd,hrow]
  simpa only [edgeCheck,he,if_true,decide_eq_true_eq] using hc

theorem route_rank (code : List Bool) (q target : Fin 285) (hfwd : forward q = true)
    (hroute : route q code = some target) : rank target ≤ rank q + code.count false := by
  induction code generalizing q with
  | nil =>
    simp only [route,Option.some.injEq] at hroute
    subst target
    simp
  | cons b bs ih =>
    simp only [route] at hroute
    split at hroute
    next hrow =>
      have he := edge_rank q b hfwd hrow
      have hn := (DispatcherInvariant.edge_closed q b hfwd hrow).1
      have hr := ih (NumericTables.target.table.row q b).next hn hroute
      cases b <;> simp at he ⊢ <;> omega
    next hrow => simp at hroute

theorem root_route_rank (code : List Bool) (target : Fin 285)
    (hroute : route treeRoot code = some target) : rank target ≤ code.count false := by
  have h := route_rank code treeRoot target forward_root hroute
  simpa only [root_rank,Nat.zero_add] using h


theorem seed_interval (start count : Nat) (h : seedChunk start count = true)
    (n : Nat) (hlo : start ≤ n) (hhi : n < start+count) : breakSeed n = true := by
  apply List.all_eq_true.mp h n
  simp only [List.mem_range']
  refine ⟨n-start,?_,?_⟩ <;> omega

theorem checked_seed (n : Nat) (hn : n < 163) : breakSeed n = true := by
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


theorem break_parent_rank (parent i : Nat) (h : nodeEdge parent true = some (.brk i)) :
    i+1 ≤ rank (state parent) := by
  have he : (fastNodes[parent]?).map (fun p => p.2) = some (.brk i) := by
    simpa only [nodeEdge,nodes_fast,if_true] using h
  have hb := mapped_lookup_bound fastNodes (fun p => p.2) parent (.brk i) he
  have hn : parent < 163 := by simpa only [nodes_size] using hb
  have hc := checked_seed parent hn
  unfold breakSeed at hc
  rw [he] at hc
  exact of_decide_eq_true hc

theorem break_prefix_zeros (code : List Bool) (i : Nat)
    (hwalk : walk 162 code = some (.brk i)) :
    ∃ pre, code = pre++[true] ∧ i+1 ≤ pre.count false ∧
      detectorRun 0 (scanWord pre) = some 0 := by
  obtain ⟨pre,parent,row,hcode,hroute,hedge,_,_,hsafe⟩ :=
    ControlInvariant.break_prefix_safe code i hwalk
  have hbound := root_route_rank pre (state parent) hroute
  have hseed := break_parent_rank parent i hedge
  exact ⟨pre,hcode,by omega,hsafe⟩

end Shared.PNP.Record285.ControlBreakRank
