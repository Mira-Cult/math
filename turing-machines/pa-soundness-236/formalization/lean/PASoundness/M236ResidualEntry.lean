import PASoundness.M236ResidualCoordinates

/-! Entry-724 cleanup and composition with the residual-coordinate loop. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

theorem residual_entry_row725 : sourceRows[725]? = some ("jump", 724, none) := by decide

theorem residual_entry_dec (base : RegisterMachine.Bank 9) (n scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAS 724 base (n+1) scratch reserve) =
      (cfgAS 725 base n scratch (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgAS, cleanup_row724, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAS, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankAS, RegisterMachine.write])

theorem residual_entry_zero (base : RegisterMachine.Bank 9) (scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAS 724 base 0 scratch reserve) = (cfgAS 726 base 0 scratch reserve, []) := by
  simp [graphSystem, graphNext, cfgAS, cleanup_row724, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAS, RegisterMachine.execute]

theorem residual_entry_jump (base : RegisterMachine.Bank 9) (a scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAS 725 base a scratch reserve) = (cfgAS 724 base a scratch reserve, []) := by
  simp [graphSystem, graphNext, cfgAS, residual_entry_row725, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

theorem residual_entry_drain_all (n : Nat) (base : RegisterMachine.Bank 9) (scratch : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgAS 724 base n scratch reserve) (2*n)
      (cfgAS 724 base 0 scratch (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgAS 724 base 0 scratch reserve)
  | succ n ih =>
    have h1 := WordEventSystem.Block.single graphSystem (residual_entry_dec base n scratch reserve)
    have h2 := WordEventSystem.Block.single graphSystem (residual_entry_jump base n scratch (reserve ++ [0]))
    have h := (h1.trans graphSystem h2).trans graphSystem (ih (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

/-- Drain `a`, preserving all other registers and appending one reserve zero per
unit, with exact silent duration. -/
theorem residual_entry_drain (n : Nat) (base : RegisterMachine.Bank 9) (scratch : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgAS 724 base n scratch reserve) (2*n+1)
      (cfgAS 726 base 0 scratch (reserve ++ List.replicate n 0)) [] := by
  have h1 := residual_entry_drain_all n base scratch reserve
  have h2 := WordEventSystem.Block.single graphSystem (residual_entry_zero base scratch (reserve ++ List.replicate n 0))
  simpa using h1.trans graphSystem h2

/-- Identify the clean a-drain exit with the entry of the residual loop. -/
theorem residual_entry_to_loop (base : RegisterMachine.Bank 9) (reserve : List Nat) (hc : base 8 = 0) :
    cfgAS 726 base 0 0 reserve =
      cfgRAC 726 (bankOnlyCount (bankAS base 0 0) (base 3)) (base 2) 0 0 reserve := by
  unfold cfgAS cfgRAC cfgAC
  congr 1
  funext i
  fin_cases i <;> simp [bankAS, bankAC, bankRest, bankOnlyCount, hc]

/-- From a prepared entry with `c = 0`, drain `a`, emit each remaining
coordinate and reach cleanup. The graph result does not assert reachability. -/
theorem residual_entry_coordinates (n : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hc : base 8 = 0) :
    ∃ duration padding, base 3 + 1 ≤ duration ∧
      graphSystem.Block (cfgAS 724 base n 0 reserve) ((2*n+1)+duration)
        (cfgRAC 749 (bankOnlyCount (bankAS base 0 0) 0) (residualTail (base 3) (base 2)) 0 0
          ((reserve ++ List.replicate n 0) ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.encodeFields (Schedule.decodeCoordinates (base 3) (base 2))) := by
  have h1 := residual_entry_drain n base 0 reserve
  rw [residual_entry_to_loop base _ hc] at h1
  have hs : bankAS base 0 0 0 = 0 := by simp [bankAS]
  obtain ⟨duration, padding, ht, h2⟩ :=
    residual_coordinates_finish (base 3) (bankAS base 0 0) (base 2)
      (reserve ++ List.replicate n 0) hs
  exact ⟨duration, padding, ht, by simpa using h1.trans graphSystem h2⟩

/-- An overflow exit with zero scratch has the prepared a-drain form. -/
theorem overflow_to_residual_entry (base : RegisterMachine.Bank 9) (count env a : Nat)
    (reserve : List Nat) (hs : base 0 = 0) :
    cfgBudgetTop 724 base count env a 0 0 reserve =
      cfgAS 724 (bankBudgetTop base count env a 0 0) a 0 reserve := by
  unfold cfgBudgetTop cfgAS
  congr 1
  funext i
  fin_cases i <;> simp [bankBudgetTop, bankBudget, bankAS, RegisterMachine.write, hs]

def overflowResidualBank (base : RegisterMachine.Bank 9) (count extra : Nat) : RegisterMachine.Bank 9 :=
  bankBudgetTop (bankAS base (count+extra+1) 0) count (base 5) extra 0 0

def overflowResidualReserve (base : RegisterMachine.Bank 9) (count : Nat) (reserve : List Nat) : List Nat :=
  (((reserve ++ List.replicate (2*count) 0) ++ [0]) ++ List.replicate count 0) ++
    List.replicate (base 4) 0

/-- In the overflow case, the prepared emitter exit silently reaches the
residual loop, which emits all remaining coordinates in order. -/
theorem overflow_then_residual_coordinates (count extra : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hc : base 8 = 0) (hcount : base 3 = count) :
    ∃ duration padding, count+1 ≤ duration ∧
      graphSystem.Block (cfgAS 103 base (count+extra+1) 0 reserve)
        ((8*count+2*(base 4)+5) + ((2*extra+1)+duration))
        (cfgRAC 749 (bankOnlyCount (bankAS (overflowResidualBank base count extra) 0 0) 0)
          (residualTail count (base 2)) 0 0
          ((overflowResidualReserve base count reserve ++ List.replicate extra 0) ++
            List.replicate padding 0))
        (PASoundness.UnaryCodec.encodeFields (Schedule.decodeCoordinates count (base 2))) := by
  have h1 := emitted_coordinate_budget_overflow count extra base reserve hc hcount
  have hs : bankAS base (count+extra+1) 0 0 = 0 := by simp [bankAS]
  rw [overflow_to_residual_entry (bankAS base (count+extra+1) 0) count (base 5) extra _ hs] at h1
  change graphSystem.Block (cfgAS 103 base (count+extra+1) 0 reserve) _
    (cfgAS 724 (overflowResidualBank base count extra) extra 0 (overflowResidualReserve base count reserve)) [] at h1
  have hc' : overflowResidualBank base count extra 8 = 0 := by
    simp [overflowResidualBank, bankBudgetTop, bankBudget]
  obtain ⟨duration, padding, ht, h2⟩ :=
    residual_entry_coordinates extra (overflowResidualBank base count extra)
      (overflowResidualReserve base count reserve) hc'
  have h := h1.trans graphSystem h2
  refine ⟨duration, padding, ?_, ?_⟩
  · simpa [overflowResidualBank, bankBudgetTop, bankBudget] using ht
  · simpa [overflowResidualBank, bankBudgetTop, bankBudget, bankAS, RegisterMachine.write] using h

/-- The four initial fields and the remaining decoded fields form exactly the
scheduled address encoding when the rank is `count + 2`. -/
theorem stage_overflow_address_word (stage count : Nat)
    (hpositive : (Cantor.unpair stage).1 = count+1) :
    stageFourWord stage ++
      PASoundness.UnaryCodec.encodeFields
        (Schedule.decodeCoordinates count (Cantor.unpair (stageRemaining stage)).2) =
      PASoundness.UnaryCodec.encodeFields
        ([ (Schedule.scheduledAddress stage).rank, (Schedule.scheduledAddress stage).certificate ] ++
          (Schedule.scheduledAddress stage).coordinates) := by
  simp [stageFourWord, stageThreeWord, stageRank, stageSecondCoordinate, stageRemaining,
    Schedule.scheduledAddress, Schedule.decodeCoordinates, PASoundness.UnaryCodec.encodeFields,
    hpositive, List.append_assoc]

/-- From a clean prepared scheduler entry, the overflowing budget branch emits
the whole scheduled address and reaches entry 749 in positive finite time.
It does not assert that this entry is reached from blank execution. -/
theorem scheduler_overflow_address_fields (stage count extra : Nat)
    (base : RegisterMachine.Bank 9) (reserve : List Nat)
    (ha : base 6 = 0) (hc : base 8 = 0) (hcount : base 3 = 0)
    (hpositive : (Cantor.unpair stage).1 = count+1)
    (hoverflow : stageSecondCoordinate stage = count+extra+1) :
    ∃ steps final, 0 < steps ∧ final.index = 749 ∧
      graphSystem.Block (cfg 0 base stage 0 0 reserve) steps final
        (PASoundness.UnaryCodec.encodeFields
          ([ (Schedule.scheduledAddress stage).rank, (Schedule.scheduledAddress stage).certificate ] ++
            (Schedule.scheduledAddress stage).coordinates)) := by
  obtain ⟨firstDuration, firstPadding, duration, padding, nextDuration, nextPadding, fourthDuration, fourthPadding,
    hf, hd, hn, hfourth, hfour⟩ :=
    scheduler_first_four_fields stage count base reserve ha hc hcount hpositive
  let b := stageFourBudgetBank base stage reserve firstPadding padding nextPadding count
  let r := stageFourBudgetReserve base stage reserve firstPadding padding nextPadding fourthPadding
  change graphSystem.Block (cfg 0 base stage 0 0 reserve) _
    (cfgAS 103 b (stageSecondCoordinate stage) 0 r) _ at hfour
  have hbc : b 8 = 0 := (stage_four_budget_bank base stage reserve firstPadding padding nextPadding count).1
  have hbn : b 3 = count := (stage_four_budget_bank base stage reserve firstPadding padding nextPadding count).2
  have hbr : b 2 = (Cantor.unpair (stageRemaining stage)).2 := by
    simp [b, stageFourBudgetBank, bankAC, bankRest]
  obtain ⟨tailDuration, tailPadding, htail, hover⟩ := overflow_then_residual_coordinates count extra b r hbc hbn
  rw [← hoverflow] at hover
  have h := hfour.trans graphSystem hover
  rw [hbr, stage_overflow_address_word stage count hpositive] at h
  refine ⟨_, _, ?_, rfl, h⟩
  simp only [stageFourDuration, stageThreeDuration, thirdFieldDuration] at *
  omega

/-- Physical lift of the whole-address overflow block, conditional on reaching
the stated clean scheduler entry on the selected blank-start execution. -/
theorem selected_scheduler_overflow_address_fields (i stage count extra : Nat)
    (base : RegisterMachine.Bank 9) (reserve : List Nat)
    (ha : base 6 = 0) (hc : base 8 = 0) (hcount : base 3 = 0)
    (hpositive : (Cantor.unpair stage).1 = count+1)
    (hoverflow : stageSecondCoordinate stage = count+extra+1)
    (h : graphSystem.run i = cfg 0 base stage 0 0 reserve) :
    ∃ steps finish, 0 < steps ∧ Good finish ∧ finish.graphState.index = 749 ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i+steps)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+steps)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++
          PASoundness.UnaryCodec.encodeFields
            ([ (Schedule.scheduledAddress stage).rank, (Schedule.scheduledAddress stage).certificate ] ++
              (Schedule.scheduledAddress stage).coordinates) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i+steps) := by
  obtain ⟨steps, final, ht, hi, block⟩ :=
    scheduler_overflow_address_fields stage count extra base reserve ha hc hcount hpositive hoverflow
  have hr : graphSystem.run (i+steps) = final := by rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i+steps) = graphSystem.prefixWord i ++
      PASoundness.UnaryCodec.encodeFields
        ([ (Schedule.scheduledAddress stage).rank, (Schedule.scheduledAddress stage).certificate ] ++
          (Schedule.scheduledAddress stage).coordinates) := by
    rw [WordEventSystem.prefix_add, h, block.output]
  obtain ⟨finish, hg, hs, hconfig⟩ := graphRefinement.related (i+steps)
  refine ⟨steps, finish, ht, hg, ?_, hconfig, ?_, ?_⟩
  · rw [hs, hr]; exact hi
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

end PASoundness.M236.OccurrenceGraph
