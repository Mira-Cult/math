import PASoundness.M236GenericEmitUnary

/-! Compose the rank field, the next address split, and its unary field.
This is a prepared-entry result, not a source or scheduler refinement. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

def secondFieldBase (base : RegisterMachine.Bank 9) (rank : Nat) : RegisterMachine.Bank 9 :=
  bankCountA (bankAS base rank 0) (base 3 + rank) 0

def secondFieldReserve (reserve : List Nat) (rank padding : Nat) : List Nat :=
  (((reserve ++ List.replicate rank 0) ++ List.replicate rank 0) ++
    List.replicate rank 0) ++ List.replicate padding 0

/-- The next emitted field is the first component of the second split.
The full source-level meaning of that component remains a separate obligation. -/
theorem rank_then_second_field (rank : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hc : base 8 = 0) :
    ∃ duration padding, base 2 + 1 ≤ duration ∧
      graphSystem.Block (cfgAS 19 base rank 0 reserve)
        ((((7*rank+3) + (3*rank+1)) + duration) +
          (7*(Cantor.unpair (base 2)).1+3))
        (cfgAS 49
          (bankAC (bankRest (secondFieldBase base rank) (Cantor.unpair (base 2)).2)
            (Cantor.unpair (base 2)).1 0)
          (Cantor.unpair (base 2)).1 0
          ((secondFieldReserve reserve rank padding ++
            List.replicate (Cantor.unpair (base 2)).1 0) ++
            List.replicate (Cantor.unpair (base 2)).1 0))
        (PASoundness.UnaryCodec.unary rank ++
          PASoundness.UnaryCodec.unary (Cantor.unpair (base 2)).1) := by
  obtain ⟨duration, padding, ht, hsplit⟩ := emit_count_then_second_unpair rank base reserve hc
  have hzero : secondFieldBase base rank 0 = 0 := by
    simp [secondFieldBase, bankCountA, bankAS]
  change graphSystem.Block (cfgAS 19 base rank 0 reserve) _
    (cfgRAC 41 (secondFieldBase base rank) (Cantor.unpair (base 2)).2
      (Cantor.unpair (base 2)).1 0 (secondFieldReserve reserve rank padding)) _ at hsplit
  rw [unpair_exit_to_emit 41 (secondFieldBase base rank) (Cantor.unpair (base 2)).2
    (Cantor.unpair (base 2)).1 0 _ hzero] at hsplit
  have hem := generic_emit_preserving_a 41 emit_rows_41 (Cantor.unpair (base 2)).1
    (bankAC (bankRest (secondFieldBase base rank) (Cantor.unpair (base 2)).2)
      (Cantor.unpair (base 2)).1 0) (secondFieldReserve reserve rank padding)
  refine ⟨duration, padding, ht, ?_⟩
  simpa [unary_as_replicate] using hsplit.trans graphSystem hem

/-- At a reachable rank-output boundary, the same two fields occur on the
literal selected blank-start run, in order, with positive elapsed time. -/
theorem selected_rank_then_second_field (i rank : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hc : base 8 = 0)
    (h : graphSystem.run i = cfgAS 19 base rank 0 reserve) :
    ∃ duration padding finish,
      base 2 + 1 ≤ duration ∧ Good finish ∧
      finish.graphState =
        cfgAS 49
          (bankAC (bankRest (secondFieldBase base rank) (Cantor.unpair (base 2)).2)
            (Cantor.unpair (base 2)).1 0)
          (Cantor.unpair (base 2)).1 0
          ((secondFieldReserve reserve rank padding ++
            List.replicate (Cantor.unpair (base 2)).1 0) ++
            List.replicate (Cantor.unpair (base 2)).1 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i + ((((7*rank+3) + (3*rank+1)) + duration) +
          (7*(Cantor.unpair (base 2)).1+3)))) ∧
      (machineWordSystem machine machineLabels).prefixWord
        (graphRefinement.boundary (i + ((((7*rank+3) + (3*rank+1)) + duration) +
          (7*(Cantor.unpair (base 2)).1+3)))) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++
          (PASoundness.UnaryCodec.unary rank ++
            PASoundness.UnaryCodec.unary (Cantor.unpair (base 2)).1) ∧
      graphRefinement.boundary i <
        graphRefinement.boundary (i + ((((7*rank+3) + (3*rank+1)) + duration) +
          (7*(Cantor.unpair (base 2)).1+3))) := by
  obtain ⟨duration, padding, ht, block⟩ := rank_then_second_field rank base reserve hc
  have hr := block.endpoint
  have hp := block.output
  obtain ⟨finish, hg, hs, hconfig⟩ := graphRefinement.related
    (i + ((((7*rank+3) + (3*rank+1)) + duration) +
      (7*(Cantor.unpair (base 2)).1+3)))
  refine ⟨duration, padding, finish, ht, hg, ?_, hconfig, ?_, ?_⟩
  · rw [WordEventSystem.run_add, h, hr] at hs
    exact hs
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, WordEventSystem.prefix_add, h, hp]
  · apply graphRefinement.boundary_strict
    omega

end PASoundness.M236.OccurrenceGraph
