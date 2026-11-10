import PASoundness.M236ResidualEntry
import PASoundness.M236FinalCleanup
import PASoundness.M236Game

/-! Overflow-branch frame and clean scheduler return. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

/-- On an overflowing prepared fourth-field exit, emit the remaining fields
and a false value, then return to the next stage with a clean bank. -/
theorem overflow_residual_false_frame (count extra : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hc : base 8 = 0) (hcount : base 3 = count) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block (cfgAS 103 base (count+extra+1) 0 reserve) duration
        (cfg 0 BlankFirst.zeros (base 1+1) 0 0 (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.encodeFields (Schedule.decodeCoordinates count (base 2)) ++ [false]) := by
  have h1 := emitted_coordinate_budget_overflow count extra base reserve hc hcount
  have hs : bankAS base (count+extra+1) 0 0 = 0 := by simp [bankAS]
  rw [overflow_to_residual_entry (bankAS base (count+extra+1) 0) count (base 5) extra _ hs] at h1
  let b := overflowResidualBank base count extra
  let r := overflowResidualReserve base count reserve
  change graphSystem.Block (cfgAS 103 base (count+extra+1) 0 reserve) _ (cfgAS 724 b extra 0 r) [] at h1
  have h2 := residual_entry_drain extra b 0 r
  have hb8 : b 8 = 0 := by simp [b, overflowResidualBank, bankBudgetTop, bankBudget]
  rw [residual_entry_to_loop b _ hb8] at h2
  have hb0 : bankAS b 0 0 0 = 0 := by simp [bankAS]
  have hb4 : bankAS b 0 0 4 = 0 := by simp [b, overflowResidualBank, bankAS, bankBudgetTop, bankBudget, RegisterMachine.write]
  obtain ⟨duration, padding, ht, h3⟩ :=
    residual_coordinates_false_frame (b 3) (bankAS b 0 0) (b 2) (r ++ List.replicate extra 0) hb0 hb4
  have hb3 : b 3 = count := by simp [b, overflowResidualBank, bankBudgetTop, bankBudget]
  have hb2 : b 2 = base 2 := by simp [b, overflowResidualBank, bankBudgetTop, bankBudget, bankAS, RegisterMachine.write]
  have hb1 : bankAS b 0 0 1 = base 1 := by simp [b, overflowResidualBank, bankBudgetTop, bankBudget, bankAS, RegisterMachine.write]
  rw [hb3, hb2, hb1] at h3
  have h := (h1.trans graphSystem h2).trans graphSystem h3
  refine ⟨(8*count+2*(base 4)+5)+(2*extra+1)+duration, 2*count+1+count+base 4+extra+padding, by omega, ?_⟩
  have hr : ((r ++ List.replicate extra 0) ++ List.replicate padding 0) =
      reserve ++ List.replicate (2*count+1+count+base 4+extra+padding) 0 := by
    dsimp only [r, overflowResidualReserve]
    change (((((reserve ++ List.replicate (2*count) 0) ++ List.replicate 1 0) ++
      List.replicate count 0) ++ List.replicate (base 4) 0) ++ List.replicate extra 0) ++
      List.replicate padding 0 = _
    simp only [List.append_assoc, ← List.replicate_add]
  rw [hr] at h
  simpa using h

/-- The mathematical value is false when the second coordinate exceeds the
bound; this lemma is independent of the physical trace. -/
theorem scheduled_overflow_selected_value (stage count extra : Nat)
    (hpositive : (Cantor.unpair stage).1 = count+1)
    (hoverflow : stageSecondCoordinate stage = count+extra+1) :
    M236Game.selectedValue (Schedule.scheduledAddress stage) = false := by
  have hy : count < stageSecondCoordinate stage := by omega
  simpa [Schedule.scheduledAddress, Schedule.decodeCoordinates, stageRemaining,
    stageSecondCoordinate, hpositive, Nat.add_assoc] using
    M236Game.selected_unbounded (Cantor.unpair (Cantor.unpair stage).2).1
      count
      (Cantor.unpair (Cantor.unpair (Cantor.unpair stage).2).2).1
      (stageSecondCoordinate stage)
      (Schedule.decodeCoordinates count (Cantor.unpair (stageRemaining stage)).2) hy

theorem encode_fields_false_frame (a : PASoundness.Observer.Address) :
    PASoundness.UnaryCodec.encodeFields ([a.rank, a.certificate] ++ a.coordinates) ++ [false] =
      PASoundness.UnaryCodec.encodeFrame a false := by
  have h (xs : List Nat) :
      PASoundness.UnaryCodec.encodeFields (xs ++ [0]) =
        PASoundness.UnaryCodec.encodeFields xs ++ [false] := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [PASoundness.UnaryCodec.encodeFields, ih, List.append_assoc]
  simp [PASoundness.UnaryCodec.encodeFrame, PASoundness.UnaryCodec.frameFields,
    PASoundness.UnaryCodec.bitNat, PASoundness.UnaryCodec.encodeFields, h, List.append_assoc]

theorem stage_four_budget_bank_stage (base : RegisterMachine.Bank 9) (stage : Nat) (reserve : List Nat)
    (firstPadding padding nextPadding count : Nat) :
    stageFourBudgetBank base stage reserve firstPadding padding nextPadding count 1 = stage := by
  simp [stageFourBudgetBank, stageFourthBase, bankAC, bankRest, bankCountTop,
    stageThreeExit, thirdFieldExit, cfgFieldTransfer, bankFieldTransfer, bankAS,
    thirdFieldBank, bankOnlyCount, secondTopState, secondDecodedBank, secondFieldBase,
    stageRankBank, rankBase, bankWith, bankCountA]

/-- A clean prepared scheduler entry in the overflowing branch produces the
exact selected source frame and returns to a clean `stage + 1` entry. -/
theorem scheduler_overflow_frame (stage count extra : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (ha : base 6 = 0) (hc : base 8 = 0) (hcount : base 3 = 0)
    (hpositive : (Cantor.unpair stage).1 = count+1)
    (hoverflow : stageSecondCoordinate stage = count+extra+1) :
    ∃ steps nextReserve, 0 < steps ∧
      graphSystem.Block (cfg 0 base stage 0 0 reserve) steps
        (cfg 0 BlankFirst.zeros (stage+1) 0 0 nextReserve)
        (PASoundness.UnaryCodec.encodeFrame (Schedule.scheduledAddress stage)
          (M236Game.selectedValue (Schedule.scheduledAddress stage))) := by
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
  have hbs : b 1 = stage := stage_four_budget_bank_stage base stage reserve firstPadding padding nextPadding count
  obtain ⟨tailDuration, tailPadding, htail, hover⟩ := overflow_residual_false_frame count extra b r hbc hbn
  rw [← hoverflow, hbr, hbs] at hover
  have h := hfour.trans graphSystem hover
  have hw : stageFourWord stage ++
      (PASoundness.UnaryCodec.encodeFields
        (Schedule.decodeCoordinates count (Cantor.unpair (stageRemaining stage)).2) ++ [false]) =
      PASoundness.UnaryCodec.encodeFrame (Schedule.scheduledAddress stage)
        (M236Game.selectedValue (Schedule.scheduledAddress stage)) := by
    rw [← List.append_assoc, stage_overflow_address_word stage count hpositive,
      encode_fields_false_frame, scheduled_overflow_selected_value stage count extra hpositive hoverflow]
  rw [hw] at h
  refine ⟨_, _, ?_, h⟩
  simp only [stageFourDuration, stageThreeDuration, thirdFieldDuration] at *
  omega

/-- The same frame and clean return occur on the literal selected machine
whenever its graph execution reaches this prepared scheduler entry. -/
theorem selected_scheduler_overflow_frame (i stage count extra : Nat)
    (base : RegisterMachine.Bank 9) (reserve : List Nat)
    (ha : base 6 = 0) (hc : base 8 = 0) (hcount : base 3 = 0)
    (hpositive : (Cantor.unpair stage).1 = count+1)
    (hoverflow : stageSecondCoordinate stage = count+extra+1)
    (h : graphSystem.run i = cfg 0 base stage 0 0 reserve) :
    ∃ steps nextReserve finish, 0 < steps ∧ Good finish ∧
      finish.graphState = cfg 0 BlankFirst.zeros (stage+1) 0 0 nextReserve ∧
      graphSystem.run (i+steps) = cfg 0 BlankFirst.zeros (stage+1) 0 0 nextReserve ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i+steps)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+steps)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++
          PASoundness.UnaryCodec.encodeFrame (Schedule.scheduledAddress stage)
            (M236Game.selectedValue (Schedule.scheduledAddress stage)) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i+steps) := by
  obtain ⟨steps, nextReserve, ht, block⟩ :=
    scheduler_overflow_frame stage count extra base reserve ha hc hcount hpositive hoverflow
  have hr : graphSystem.run (i+steps) = cfg 0 BlankFirst.zeros (stage+1) 0 0 nextReserve := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i+steps) = graphSystem.prefixWord i ++
      PASoundness.UnaryCodec.encodeFrame (Schedule.scheduledAddress stage)
        (M236Game.selectedValue (Schedule.scheduledAddress stage)) := by
    rw [WordEventSystem.prefix_add, h, block.output]
  obtain ⟨finish, hg, hs, hconfig⟩ := graphRefinement.related (i+steps)
  refine ⟨steps, nextReserve, finish, ht, hg, hs.trans hr, hr, hconfig, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

end PASoundness.M236.OccurrenceGraph
