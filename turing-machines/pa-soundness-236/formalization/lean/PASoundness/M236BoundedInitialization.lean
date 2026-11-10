import PASoundness.M236RepeatedShift
import PASoundness.M236InitialEnvironment

/-! Prepared bounded-coordinate bit extraction followed by environment initialization. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

/-- The bit-extraction output has the environment routine's bank view. -/
theorem half_to_environment (index : Nat) (base : RegisterMachine.Bank 9)
    (a b c scratch : Nat) (reserve : List Nat) :
    cfgHalf index base a b c scratch reserve =
      cfgBudget index (bankHalf base a b c scratch) (base 3) (base 5) a c reserve := by
  unfold cfgHalf cfgBudget
  congr 1
  funext i
  fin_cases i <;> simp [bankHalf, bankBudget]

def boundedBitBank (base : RegisterMachine.Bank 9) (n : Nat) : RegisterMachine.Bank 9 :=
  bankHalf (bankBudget (bankAS base n 0) (base 3) (base 5+n) n 0)
    0 (if (base 7).testBit n then 1 else 0) 0 0

def budgetExitBitBank (base : RegisterMachine.Bank 9) (count env n : Nat) : RegisterMachine.Bank 9 :=
  bankHalf (bankBudget base count env n 0) 0 (if (base 7).testBit n then 1 else 0) 0 0

/-- From the successful-budget exit itself, compute the indexed bit and the
initial environment, retaining the other bank registers and emitting nothing. -/
theorem budget_exit_then_initialize (n count env : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hs : base 0 = 0) :
    ∃ duration padding, n+2 ≤ duration ∧
      graphSystem.Block (cfgBudget 119 base count env n 0 reserve) duration
        (cfgBudget 161 (budgetExitBitBank base count env n) count (Cantor.pair env 0) 0 0
          (reserve ++ List.replicate padding 0)) [] := by
  have he := budget_exit_to_half base count env n reserve hs
  let H := bankBudget base count env n 0
  let bit := if (base 7).testBit n then 1 else 0
  obtain ⟨d1, p1, hd1, h1⟩ := repeated_shift_bit n (base 7) H reserve
  rw [← he] at h1
  have hH3 : H 3 = count := by simp [H, bankBudget]
  have hH5 : H 5 = env := by simp [H, bankBudget]
  rw [half_to_environment 145 H 0 bit 0 0 _, hH3, hH5] at h1
  obtain ⟨d2, p2, hd2, h2⟩ := initialize_environment env (budgetExitBitBank base count env n)
    count (reserve ++ List.replicate p1 0)
  have h := h1.trans graphSystem h2
  refine ⟨d1+d2, p1+p2, by omega, ?_⟩
  have hr : (reserve ++ List.replicate p1 0) ++ List.replicate p2 0 =
      reserve ++ List.replicate (p1+p2) 0 := by
    simp only [List.append_assoc, ← List.replicate_add]
  rw [hr] at h
  simpa [H, bit, budgetExitBitBank] using h

/-- Physical lift from a reached prepared successful-budget exit. -/
theorem selected_budget_exit_then_initialize (i n count env : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hs : base 0 = 0)
    (h : graphSystem.run i = cfgBudget 119 base count env n 0 reserve) :
    ∃ duration padding finish, n+2 ≤ duration ∧ Good finish ∧
      finish.graphState = cfgBudget 161 (budgetExitBitBank base count env n) count (Cantor.pair env 0) 0 0
        (reserve ++ List.replicate padding 0) ∧
      graphSystem.run (i+duration) = cfgBudget 161 (budgetExitBitBank base count env n) count (Cantor.pair env 0) 0 0
        (reserve ++ List.replicate padding 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run (graphRefinement.boundary (i+duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i+duration) := by
  obtain ⟨duration, padding, ht, block⟩ := budget_exit_then_initialize n count env base reserve hs
  have hr : graphSystem.run (i+duration) = cfgBudget 161 (budgetExitBitBank base count env n) count (Cantor.pair env 0) 0 0
      (reserve ++ List.replicate padding 0) := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i+duration) = graphSystem.prefixWord i := by
    rw [WordEventSystem.prefix_add, h, block.output, List.append_nil]
  obtain ⟨finish, hg, hstate, hconfig⟩ := graphRefinement.related (i+duration)
  refine ⟨duration, padding, finish, ht, hg, hstate.trans hr, hr, hconfig, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

/-- Starting just after the second-coordinate emitter, the successful budget
branch computes its selected bit and initializes the environment. The input
base need not have zero env; the exact result is `pair (base 5+n) 0`. -/
theorem budget_success_then_initialize (n remaining : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hc : base 8 = 0) (hcount : base 3 = remaining+n) :
    ∃ duration padding, n+2 ≤ duration ∧
      graphSystem.Block (cfgAS 103 base n 0 reserve) ((10*n+2)+duration)
        (cfgBudget 161 (boundedBitBank base n) (base 3) (Cantor.pair (base 5+n) 0) 0 0
          (reserve ++ List.replicate (3*n+padding) 0)) [] := by
  obtain ⟨d1, p1, hd1, h1⟩ := budget_success_then_bit n remaining base reserve hc hcount
  let H := bankBudget (bankAS base n 0) (base 3) (base 5+n) n 0
  let bit := if (base 7).testBit n then 1 else 0
  have hH3 : H 3 = base 3 := by simp [H, bankBudget]
  have hH5 : H 5 = base 5+n := by simp [H, bankBudget]
  rw [half_to_environment 145 H 0 bit 0 0 _, hH3, hH5] at h1
  obtain ⟨d2, p2, hd2, h2⟩ := initialize_environment (base 5+n) (boundedBitBank base n)
    (base 3) (reserve ++ List.replicate (3*n+p1) 0)
  have h := h1.trans graphSystem h2
  refine ⟨d1+d2, p1+p2, by omega, ?_⟩
  have hr : (reserve ++ List.replicate (3*n+p1) 0) ++ List.replicate p2 0 =
      reserve ++ List.replicate (3*n+(p1+p2)) 0 := by
    simp only [List.append_assoc, ← List.replicate_add, Nat.add_assoc]
  rw [hr] at h
  simpa [H, bit, boundedBitBank, Nat.add_assoc] using h

/-- Exact retained register effects at the initialized boundary. -/
theorem bounded_initialized_registers (n : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) :
    let s := cfgBudget 161 (boundedBitBank base n) (base 3) (Cantor.pair (base 5+n) 0) 0 0 reserve
    s.registers 0 = 0 ∧ s.registers 1 = base 1 ∧ s.registers 2 = base 2 ∧
    s.registers 3 = base 3 ∧ s.registers 4 = base 4 ∧
    s.registers 5 = Cantor.pair (base 5+n) 0 ∧ s.registers 6 = 0 ∧
    s.registers 7 = (if (base 7).testBit n then 1 else 0) ∧ s.registers 8 = 0 := by
  simp [cfgBudget, boundedBitBank, bankBudget, bankHalf, bankAS]

/-- The four-field scheduler block continues through the bounded branch to
the initialized environment. Its previously emitted word is preserved exactly. -/
theorem scheduler_bounded_then_initialize (stage count : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (ha : base 6 = 0) (hc : base 8 = 0) (hcount : base 3 = 0)
    (hpositive : (Cantor.unpair stage).1 = count+1)
    (hbudget : stageSecondCoordinate stage ≤ count) :
    ∃ firstDuration firstPadding duration padding nextDuration nextPadding fourthDuration fourthPadding tailDuration tailPadding,
      stage+1 ≤ firstDuration ∧ (Cantor.unpair stage).2+1 ≤ duration ∧
      (Cantor.unpair (Cantor.unpair stage).2).2+1 ≤ nextDuration ∧
      stageRemaining stage+1 ≤ fourthDuration ∧ stageSecondCoordinate stage+2 ≤ tailDuration ∧
      graphSystem.Block (cfg 0 base stage 0 0 reserve)
        (stageFourDuration base stage firstDuration duration nextDuration fourthDuration +
          ((10*stageSecondCoordinate stage+2)+tailDuration))
        (let b := stageFourBudgetBank base stage reserve firstPadding padding nextPadding count
         let r := stageFourBudgetReserve base stage reserve firstPadding padding nextPadding fourthPadding
         let q := stageSecondCoordinate stage
         cfgBudget 161 (boundedBitBank b q) count (Cantor.pair (b 5+q) 0) 0 0
           (r ++ List.replicate (3*q+tailPadding) 0))
        (stageFourWord stage) := by
  obtain ⟨firstDuration, firstPadding, duration, padding, nextDuration, nextPadding, fourthDuration, fourthPadding,
    hf, hd, hn, hfourth, hfour⟩ :=
    scheduler_first_four_fields stage count base reserve ha hc hcount hpositive
  let b := stageFourBudgetBank base stage reserve firstPadding padding nextPadding count
  let r := stageFourBudgetReserve base stage reserve firstPadding padding nextPadding fourthPadding
  let q := stageSecondCoordinate stage
  change graphSystem.Block (cfg 0 base stage 0 0 reserve) _ (cfgAS 103 b q 0 r) _ at hfour
  have hbc : b 8 = 0 := (stage_four_budget_bank base stage reserve firstPadding padding nextPadding count).1
  have hbn : b 3 = count := (stage_four_budget_bank base stage reserve firstPadding padding nextPadding count).2
  have hexists : ∃ remaining, b 3 = remaining+q := by
    refine ⟨count-q, ?_⟩
    dsimp [q] at *
    omega
  obtain ⟨remaining, hremaining⟩ := hexists
  obtain ⟨tailDuration, tailPadding, htail, htailblock⟩ :=
    budget_success_then_initialize q remaining b r hbc hremaining
  rw [hbn] at htailblock
  refine ⟨firstDuration, firstPadding, duration, padding, nextDuration, nextPadding, fourthDuration, fourthPadding,
    tailDuration, tailPadding, hf, hd, hn, hfourth, htail, ?_⟩
  simpa [b, r, q] using hfour.trans graphSystem htailblock

/-- Physical lift conditional on actual reachability of the prepared entry. -/
theorem selected_budget_success_then_initialize (i n remaining : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hc : base 8 = 0) (hcount : base 3 = remaining+n)
    (h : graphSystem.run i = cfgAS 103 base n 0 reserve) :
    ∃ duration padding finish, n+2 ≤ duration ∧ Good finish ∧
      finish.graphState = cfgBudget 161 (boundedBitBank base n) (base 3) (Cantor.pair (base 5+n) 0) 0 0
        (reserve ++ List.replicate (3*n+padding) 0) ∧
      graphSystem.run (i+(10*n+2)+duration) =
        cfgBudget 161 (boundedBitBank base n) (base 3) (Cantor.pair (base 5+n) 0) 0 0
          (reserve ++ List.replicate (3*n+padding) 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i+(10*n+2)+duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+(10*n+2)+duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i+(10*n+2)+duration) := by
  obtain ⟨duration, padding, ht, block⟩ := budget_success_then_initialize n remaining base reserve hc hcount
  have hr : graphSystem.run (i+((10*n+2)+duration)) =
      cfgBudget 161 (boundedBitBank base n) (base 3) (Cantor.pair (base 5+n) 0) 0 0
        (reserve ++ List.replicate (3*n+padding) 0) := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i+((10*n+2)+duration)) = graphSystem.prefixWord i := by
    rw [WordEventSystem.prefix_add, h, block.output, List.append_nil]
  obtain ⟨finish, hg, hs, hconfig⟩ := graphRefinement.related (i+((10*n+2)+duration))
  refine ⟨duration, padding, finish, ht, hg, ?_, ?_, ?_, ?_, ?_⟩
  · exact hs.trans hr
  · simpa [Nat.add_assoc] using hr
  · simpa [Nat.add_assoc] using hconfig
  · simpa [Nat.add_assoc, graphRefinement.prefix_eq] using hp
  · apply graphRefinement.boundary_strict
    omega

end PASoundness.M236.OccurrenceGraph
