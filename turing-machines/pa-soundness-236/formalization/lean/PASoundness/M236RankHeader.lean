import PASoundness.M236GraphUnpair
import PASoundness.M236GraphEmitUnary
/-! Compose the first unpairing and rank-field emission. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

def rankBase (base : RegisterMachine.Bank 9) (rest a : Nat) : RegisterMachine.Bank 9 :=
  bankAC (bankRest base rest) a 0

theorem rank_entry_convert (base : RegisterMachine.Bank 9) (rest a : Nat)
    (reserve : List Nat) (hzero : base 0 = 0) :
    cfgRAC 19 base rest a 0 reserve = cfgAS 19 (rankBase base rest a) a 0 reserve := by
  unfold cfgRAC cfgAC cfgAS rankBase
  congr 1
  funext i
  fin_cases i <;> simp [bankAC, bankAS, bankRest, hzero]

/-- The unpairing and unary rank field, for arbitrary stage code. -/
theorem unpair_then_emit_rank (n : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hzero : base 0 = 0) :
    ∃ duration padding, n+1 ≤ duration ∧
      graphSystem.Block (cfgRAC 7 base n 0 0 reserve)
        (duration + (7*((Cantor.unpair n).1+1)+3))
        (cfgAS 27 (rankBase base (Cantor.unpair n).2 ((Cantor.unpair n).1+1))
          ((Cantor.unpair n).1+1) 0
          (((reserve ++ List.replicate padding 0) ++ List.replicate ((Cantor.unpair n).1+1) 0) ++
            List.replicate ((Cantor.unpair n).1+1) 0))
        (PASoundness.UnaryCodec.unary ((Cantor.unpair n).1+1)) := by
  obtain ⟨duration, padding, ht, hscan⟩ := unpair_to_rank_entry n base reserve
  have heq := rank_entry_convert base (Cantor.unpair n).2 ((Cantor.unpair n).1+1)
    (reserve ++ List.replicate padding 0) hzero
  rw [heq] at hscan
  have hem := emit_preserving_a ((Cantor.unpair n).1+1)
    (rankBase base (Cantor.unpair n).2 ((Cantor.unpair n).1+1))
    (reserve ++ List.replicate padding 0)
  refine ⟨duration, padding, ht, ?_⟩
  simpa only [List.nil_append, unary_as_replicate] using hscan.trans graphSystem hem

/-- Lift the exact rank field to any reachable selected-machine entry with
zero scratch. -/
theorem selected_unpair_emit_rank (i n : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hzero : base 0 = 0)
    (h : graphSystem.run i = cfgRAC 7 base n 0 0 reserve) :
    ∃ duration padding finish,
      n+1 ≤ duration ∧ Good finish ∧
      finish.graphState =
        cfgAS 27 (rankBase base (Cantor.unpair n).2 ((Cantor.unpair n).1+1))
          ((Cantor.unpair n).1+1) 0
          (((reserve ++ List.replicate padding 0) ++ List.replicate ((Cantor.unpair n).1+1) 0) ++
            List.replicate ((Cantor.unpair n).1+1) 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i + (duration + (7*((Cantor.unpair n).1+1)+3)))) ∧
      (machineWordSystem machine machineLabels).prefixWord
          (graphRefinement.boundary (i + (duration + (7*((Cantor.unpair n).1+1)+3)))) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++
          PASoundness.UnaryCodec.unary ((Cantor.unpair n).1+1) ∧
      graphRefinement.boundary i <
        graphRefinement.boundary (i + (duration + (7*((Cantor.unpair n).1+1)+3))) := by
  obtain ⟨duration, padding, ht, block⟩ := unpair_then_emit_rank n base reserve hzero
  have hr : graphSystem.run (i + (duration + (7*((Cantor.unpair n).1+1)+3))) =
      cfgAS 27 (rankBase base (Cantor.unpair n).2 ((Cantor.unpair n).1+1))
        ((Cantor.unpair n).1+1) 0
        (((reserve ++ List.replicate padding 0) ++ List.replicate ((Cantor.unpair n).1+1) 0) ++
          List.replicate ((Cantor.unpair n).1+1) 0) := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i + (duration + (7*((Cantor.unpair n).1+1)+3))) =
      graphSystem.prefixWord i ++ PASoundness.UnaryCodec.unary ((Cantor.unpair n).1+1) := by
    rw [WordEventSystem.prefix_add, h, block.output]
  obtain ⟨finish, hg, hs, hc⟩ := graphRefinement.related (i + (duration + (7*((Cantor.unpair n).1+1)+3)))
  refine ⟨duration, padding, finish, ht, hg, hs.trans hr, hc, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega
/-- The actual blank-start machine emits its first complete rank field,
`[true, false]`, at a finite positive graph boundary. -/
theorem initial_rank_field_on_selected :
    ∃ duration finish,
      1 ≤ duration ∧ Good finish ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (2 + (duration + 10))) ∧
      (machineWordSystem machine machineLabels).prefixWord
        (graphRefinement.boundary (2 + (duration + 10))) = [true, false] := by
  have hg := (copy_at_graph_run 0 0 BlankFirst.zeros 0 BlankFirst.reserve initial_copy_entry).2
  have hg2 : graphSystem.prefixWord 2 = [] := by simpa using hg
  have hp2 : (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary 2) = [] := by
    rw [graphRefinement.prefix_eq, hg2]
  obtain ⟨duration, padding, finish, ht, hgood, hstate, hconfig, hprefix, hpositive⟩ :=
    selected_unpair_emit_rank 2 0 BlankFirst.zeros BlankFirst.reserve rfl initial_diagonal_entry
  refine ⟨duration, finish, ht, hgood, ?_, ?_⟩
  · simpa [Cantor.unpair, Cantor.unpairAux] using hconfig
  · simpa [Cantor.unpair, Cantor.unpairAux, PASoundness.UnaryCodec.unary, hp2] using hprefix

/-- The first copy exit is the unpair entry when the a and c work registers
are initially zero. Other registers are preserved by the explicit bank. -/
theorem copy_exit_to_unpair (base : RegisterMachine.Bank 9) (n : Nat) (reserve : List Nat)
    (ha : base 6 = 0) (hc : base 8 = 0) :
    cfg 7 base n n 0 reserve = cfgRAC 7 (bankWith base n n 0) n 0 0 reserve := by
  unfold cfg cfgRAC cfgAC
  congr 1
  funext i
  fin_cases i <;> simp [bankWith, bankAC, bankRest, ha, hc]

/-- From a clean scheduler entry, copy, unpair and emit the exact rank field
for any stage code; this is still only the first field of the record. -/
theorem scheduler_rank_field (n : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (ha : base 6 = 0) (hc : base 8 = 0) :
    ∃ duration padding, n+1 ≤ duration ∧
      graphSystem.Block (cfg 0 base n 0 0 reserve)
        ((7*n+2) + (duration + (7*((Cantor.unpair n).1+1)+3)))
        (cfgAS 27 (rankBase (bankWith base n n 0) (Cantor.unpair n).2 ((Cantor.unpair n).1+1))
          ((Cantor.unpair n).1+1) 0
          (((((reserve ++ List.replicate n 0) ++ List.replicate n 0) ++ List.replicate padding 0) ++
            List.replicate ((Cantor.unpair n).1+1) 0) ++ List.replicate ((Cantor.unpair n).1+1) 0))
        (PASoundness.UnaryCodec.unary ((Cantor.unpair n).1+1)) := by
  have hcopy : graphSystem.Block (cfg 0 base n 0 0 reserve) (7*n+2)
      (cfg 7 base n n 0 ((reserve ++ List.replicate n 0) ++ List.replicate n 0)) [] := by
    simpa only [Nat.zero_add] using copy_stage n base 0 reserve
  rw [copy_exit_to_unpair base n _ ha hc] at hcopy
  obtain ⟨duration, padding, ht, hrest⟩ := unpair_then_emit_rank n (bankWith base n n 0)
    ((reserve ++ List.replicate n 0) ++ List.replicate n 0) (by simp [bankWith])
  refine ⟨duration, padding, ht, ?_⟩
  simpa only [List.nil_append] using hcopy.trans graphSystem hrest


/-- The selected blank-start execution realizes this field at any graph boundary
whose clean scheduler-entry invariant is established. -/
theorem selected_scheduler_rank_field (i n : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (ha : base 6 = 0) (hc : base 8 = 0)
    (h : graphSystem.run i = cfg 0 base n 0 0 reserve) :
    ∃ duration padding finish,
      n+1 ≤ duration ∧ Good finish ∧
      finish.graphState =
        cfgAS 27 (rankBase (bankWith base n n 0) (Cantor.unpair n).2 ((Cantor.unpair n).1+1))
          ((Cantor.unpair n).1+1) 0
          (((((reserve ++ List.replicate n 0) ++ List.replicate n 0) ++ List.replicate padding 0) ++
            List.replicate ((Cantor.unpair n).1+1) 0) ++ List.replicate ((Cantor.unpair n).1+1) 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i + ((7*n+2) + (duration + (7*((Cantor.unpair n).1+1)+3))))) ∧
      (machineWordSystem machine machineLabels).prefixWord
          (graphRefinement.boundary (i + ((7*n+2) + (duration + (7*((Cantor.unpair n).1+1)+3))))) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++
          PASoundness.UnaryCodec.unary ((Cantor.unpair n).1+1) ∧
      graphRefinement.boundary i <
        graphRefinement.boundary (i + ((7*n+2) + (duration + (7*((Cantor.unpair n).1+1)+3)))) := by
  obtain ⟨duration, padding, ht, block⟩ := scheduler_rank_field n base reserve ha hc
  have hr : graphSystem.run (i + ((7*n+2) + (duration + (7*((Cantor.unpair n).1+1)+3)))) =
      cfgAS 27 (rankBase (bankWith base n n 0) (Cantor.unpair n).2 ((Cantor.unpair n).1+1))
        ((Cantor.unpair n).1+1) 0
        (((((reserve ++ List.replicate n 0) ++ List.replicate n 0) ++ List.replicate padding 0) ++
          List.replicate ((Cantor.unpair n).1+1) 0) ++ List.replicate ((Cantor.unpair n).1+1) 0) := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i + ((7*n+2) + (duration + (7*((Cantor.unpair n).1+1)+3)))) =
      graphSystem.prefixWord i ++ PASoundness.UnaryCodec.unary ((Cantor.unpair n).1+1) := by
    rw [WordEventSystem.prefix_add, h, block.output]
  obtain ⟨finish, hg, hs, hc'⟩ := graphRefinement.related
    (i + ((7*n+2) + (duration + (7*((Cantor.unpair n).1+1)+3))))
  refine ⟨duration, padding, finish, ht, hg, hs.trans hr, hc', ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

end PASoundness.M236.OccurrenceGraph
