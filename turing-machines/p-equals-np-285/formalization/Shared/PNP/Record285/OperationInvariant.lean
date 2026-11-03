import Shared.PNP.Record285.OperationInvariantCheck

/-! Every preserving route to a checked operation terminal passes the
five-zero detector, with an arbitrary path and no reachability hypothesis. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.OperationInvariant
open Shared.Beeping.Machines
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.DispatcherInvariant (forward forward_root detector_append)
open Shared.PNP.Record285.OperationInvariantData
open Shared.PNP.Record285.Grammar (decTerminal halfTerminal)

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

/-- A checked preserving edge stays forward-reachable, and every valid
reverse detector suffix can be extended one step without reaching five zeros. -/
theorem edge_closed (q : Fin 285) (b : Bool) (hfwd : forward q = true)
    (hrow : (NumericTables.target.table.row q b).write = b ∧
      (NumericTables.target.table.row q b).move = .right ∧
      (NumericTables.target.table.row q b).beep = false) :
    let next := (NumericTables.target.table.row q b).next
    forward next = true ∧
      ∀ d, d < 5 → backward next d = true →
        ∃ d', detectorNext d b = some d' ∧ backward q d' = true := by
  have hc := checked_edge q b
  have he : (forward q && decide ((NumericTables.target.table.row q b).write = b ∧
      (NumericTables.target.table.row q b).move = .right ∧
      (NumericTables.target.table.row q b).beep = false)) = true := by simp [hfwd,hrow]
  simp only [edgeCheck,he,if_true,Bool.and_eq_true] at hc
  refine ⟨hc.1,?_⟩
  intro d hd hb
  have hv := List.all_eq_true.mp hc.2 d (List.mem_range.mpr hd)
  simp only [hb,if_true] at hv
  cases hn : detectorNext d b with
  | none => simp [hn] at hv
  | some next =>
    refine ⟨next,rfl,?_⟩
    simpa only [hn] using hv

theorem backward_root_bound (d : Nat) (hd : d < 5) (hb : backward treeRoot d = true) : d < 4 := by
  by_cases h : d < 4
  · exact h
  have heq : d = 4 := by omega
  subst d
  have hf : backward treeRoot 4 = false := by decide
  rw [hf] at hb
  contradiction

theorem reverse_safe (code : List Bool) (q target : Fin 285)
    (hseed : backward target 0 = true) (hfwd : forward q = true)
    (hroute : route q code = some target) :
    ∃ d, d < 5 ∧ detectorRun 0 code.reverse = some d ∧ backward q d = true := by
  induction code generalizing q with
  | nil =>
    simp only [route,Option.some.injEq] at hroute
    subst q
    exact ⟨0,by decide,rfl,hseed⟩
  | cons b bs ih =>
    simp only [route] at hroute
    split at hroute
    next hrow =>
      have hc := edge_closed q b hfwd hrow
      obtain ⟨d,hd,hrev,hback⟩ := ih (NumericTables.target.table.row q b).next hc.1 hroute
      obtain ⟨d',hnext,hback'⟩ := hc.2 d hd hback
      have hd' := detector_bound d d' b hd hnext
      refine ⟨d',hd',?_,hback'⟩
      simp only [List.reverse_cons,detector_append,hrev,Option.bind_some,detectorRun,hnext]
    next hrow => simp at hroute

theorem route_is_safe (code : List Bool) (target : Fin 285)
    (hseed : backward target 0 = true) (hroute : route treeRoot code = some target) :
    detectorRun 0 (scanWord code) = some 0 := by
  obtain ⟨d,hd,hrev,hback⟩ := reverse_safe code treeRoot target hseed forward_root hroute
  have hlt := backward_root_bound d hd hback
  simp only [scanWord,detector_append,hrev,Option.bind_some,detectorRun,detectorNext,
    Bool.false_eq_true,if_false,if_true,if_pos hlt]

theorem dec_route_safe (code : List Bool) (i : Nat) (hi : i < 15)
    (hroute : route treeRoot code = some (decTerminal i)) :
    detectorRun 0 (scanWord code) = some 0 := by
  apply route_is_safe code (decTerminal i) ?_ hroute
  exact List.all_eq_true.mp dec_seed_all i (List.mem_range.mpr hi)

theorem half_route_safe (code : List Bool) (i : Nat) (hi : i < 4)
    (hroute : route treeRoot code = some (halfTerminal i)) :
    detectorRun 0 (scanWord code) = some 0 := by
  apply route_is_safe code (halfTerminal i) ?_ hroute
  exact List.all_eq_true.mp half_seed_all i (List.mem_range.mpr hi)

theorem beep_route_safe (code : List Bool) (hroute : route treeRoot code = some ⟨121,by decide⟩) :
    detectorRun 0 (scanWord code) = some 0 :=
  route_is_safe code ⟨121,by decide⟩ beep_seed hroute

end Shared.PNP.Record285.OperationInvariant
