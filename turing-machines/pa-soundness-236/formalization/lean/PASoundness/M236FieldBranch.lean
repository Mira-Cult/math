import PASoundness.M236FieldTransfer

/-! The positive-counter branch to the next address split. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

def bankOnlyCount (base : RegisterMachine.Bank 9) (count : Nat) : RegisterMachine.Bank 9 :=
  fun i => if i = 3 then count else base i

def cfgOnlyCount (index : Nat) (base : RegisterMachine.Bank 9) (count : Nat)
    (reserve : List Nat) : GraphState := ⟨index, bankOnlyCount base count, reserve⟩

theorem field_branch_row52 : sourceRows[52]? = some ("3.k.count.decnz", 53, some 54) := by decide
theorem field_branch_row53 : sourceRows[53]? = some ("jump", 57, none) := by decide

theorem field_branch_dec (base : RegisterMachine.Bank 9) (n : Nat) (reserve : List Nat) :
    graphSystem.step (cfgOnlyCount 52 base (n+1) reserve) =
      (cfgOnlyCount 53 base n (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgOnlyCount, field_branch_row52, nextIndex, nextBank,
    nextReserve, incRegister, decRegister, outputForOp, bankOnlyCount,
    RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankOnlyCount, RegisterMachine.write])

theorem field_branch_jump (base : RegisterMachine.Bank 9) (count : Nat) (reserve : List Nat) :
    graphSystem.step (cfgOnlyCount 53 base count reserve) =
      (cfgOnlyCount 57 base count reserve, []) := by
  simp [graphSystem, graphNext, cfgOnlyCount, field_branch_row53, nextIndex, nextBank,
    nextReserve, incRegister, decRegister, outputForOp]

/-- A positive counter takes the silent branch to the next unpairing entry. -/
theorem positive_count_to_unpair (base : RegisterMachine.Bank 9) (n : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgOnlyCount 52 base (n+1) reserve) 2
      (cfgOnlyCount 57 base n (reserve ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (field_branch_dec base n reserve)
  have h2 := WordEventSystem.Block.single graphSystem (field_branch_jump base n (reserve ++ [0]))
  simpa using h1.trans graphSystem h2

theorem second_top_count (base : RegisterMachine.Bank 9) (rank : Nat)
    (reserve : List Nat) (padding : Nat) :
    secondTopState base rank reserve padding =
      cfgOnlyCount 52 (secondTopState base rank reserve padding).registers (base 3 + rank)
        (secondTopState base rank reserve padding).reserve := by
  simp only [secondTopState, cfgFieldTransfer, cfgOnlyCount]
  congr 1
  funext i
  by_cases hi : i = 3
  · subst i
    simp [bankOnlyCount, bankFieldTransfer, bankAS, secondDecodedBank, bankAC, bankRest,
      secondFieldBase, bankCountA]
  · simp [bankOnlyCount, hi]

/-- The two fields and top transfer continue to entry 57 whenever the
resulting counter is positive. The count hypothesis is explicit. -/
theorem rank_second_field_positive_branch (rank n : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hc : base 8 = 0) (hcount : base 3 + rank = n+1) :
    ∃ duration padding, base 2 + 1 ≤ duration ∧
      graphSystem.Block (cfgAS 19 base rank 0 reserve)
        (secondTopDuration rank (base 2) duration + 2)
        (cfgOnlyCount 57 (secondTopState base rank reserve padding).registers n
          ((secondTopState base rank reserve padding).reserve ++ [0]))
        (PASoundness.UnaryCodec.unary rank ++
          PASoundness.UnaryCodec.unary (Cantor.unpair (base 2)).1) := by
  obtain ⟨duration, padding, ht, block⟩ := rank_second_field_then_top rank base reserve hc
  change graphSystem.Block (cfgAS 19 base rank 0 reserve)
    (secondTopDuration rank (base 2) duration) (secondTopState base rank reserve padding) _ at block
  rw [second_top_count base rank reserve padding, hcount] at block
  have hbranch := positive_count_to_unpair (secondTopState base rank reserve padding).registers n
    (secondTopState base rank reserve padding).reserve
  refine ⟨duration, padding, ht, ?_⟩
  simpa using block.trans graphSystem hbranch

/-- A counter-only state enters the unpairing schema when its work registers
`a` and `c` are zero. -/
theorem count_entry_to_unpair (base : RegisterMachine.Bank 9) (count : Nat)
    (reserve : List Nat) (ha : base 6 = 0) (hc : base 8 = 0) :
    cfgOnlyCount 57 base count reserve =
      cfgRAC 57 (bankOnlyCount base count) (base 2) 0 0 reserve := by
  unfold cfgOnlyCount cfgRAC cfgAC
  congr 1
  funext i
  fin_cases i <;> simp [bankOnlyCount, bankAC, bankRest, ha, hc]

theorem second_top_work_zero (base : RegisterMachine.Bank 9) (rank : Nat)
    (reserve : List Nat) (padding : Nat) :
    (secondTopState base rank reserve padding).registers 6 = 0 ∧
      (secondTopState base rank reserve padding).registers 8 = 0 := by
  simp [secondTopState, cfgFieldTransfer, bankFieldTransfer, bankAS,
    secondDecodedBank, bankAC, bankRest]

theorem second_top_rest (base : RegisterMachine.Bank 9) (rank : Nat)
    (reserve : List Nat) (padding : Nat) :
    (secondTopState base rank reserve padding).registers 2 = (Cantor.unpair (base 2)).2 := by
  simp [secondTopState, cfgFieldTransfer, bankFieldTransfer, bankAS,
    secondDecodedBank, bankAC, bankRest]

/-- Under the positive-counter condition, the next checked unpairing computes
the Cantor inverse of the remaining address code without further output. -/
theorem rank_second_field_then_next_unpair (rank n : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hc : base 8 = 0) (hcount : base 3 + rank = n+1) :
    ∃ duration padding nextDuration nextPadding,
      base 2 + 1 ≤ duration ∧ (Cantor.unpair (base 2)).2 + 1 ≤ nextDuration ∧
      graphSystem.Block (cfgAS 19 base rank 0 reserve)
        ((secondTopDuration rank (base 2) duration + 2) + nextDuration)
        (cfgRAC 68 (bankOnlyCount (secondTopState base rank reserve padding).registers n)
          (Cantor.unpair (Cantor.unpair (base 2)).2).2
          (Cantor.unpair (Cantor.unpair (base 2)).2).1 0
          (((secondTopState base rank reserve padding).reserve ++ [0]) ++
            List.replicate nextPadding 0))
        (PASoundness.UnaryCodec.unary rank ++
          PASoundness.UnaryCodec.unary (Cantor.unpair (base 2)).1) := by
  obtain ⟨duration, padding, ht, block⟩ :=
    rank_second_field_positive_branch rank n base reserve hc hcount
  obtain ⟨ha, hc'⟩ := second_top_work_zero base rank reserve padding
  rw [count_entry_to_unpair (secondTopState base rank reserve padding).registers n
    ((secondTopState base rank reserve padding).reserve ++ [0]) ha hc',
    second_top_rest base rank reserve padding] at block
  obtain ⟨nextDuration, nextPadding, hn, hnext⟩ :=
    unpair_at_57 (Cantor.unpair (base 2)).2
      (bankOnlyCount (secondTopState base rank reserve padding).registers n)
      ((secondTopState base rank reserve padding).reserve ++ [0])
  refine ⟨duration, padding, nextDuration, nextPadding, ht, hn, ?_⟩
  simpa using block.trans graphSystem hnext

def thirdFieldValue (base : RegisterMachine.Bank 9) : Nat :=
  (Cantor.unpair (Cantor.unpair (base 2)).2).1

def thirdFieldBank (base : RegisterMachine.Bank 9) (rank : Nat) (reserve : List Nat)
    (padding count : Nat) : RegisterMachine.Bank 9 :=
  bankAC (bankRest (bankOnlyCount (secondTopState base rank reserve padding).registers count)
    (Cantor.unpair (Cantor.unpair (base 2)).2).2) (thirdFieldValue base) 0

def thirdFieldReserve (base : RegisterMachine.Bank 9) (rank : Nat) (reserve : List Nat)
    (padding nextPadding : Nat) : List Nat :=
  ((secondTopState base rank reserve padding).reserve ++ [0]) ++ List.replicate nextPadding 0

/-- The positive branch reaches and emits the next field, then silently moves
its value into `b`. Source-level field meaning and future iterations are not
assumed or established. -/
theorem rank_through_third_field (rank count : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hc : base 8 = 0) (hcount : base 3 + rank = count+1) :
    ∃ duration padding nextDuration nextPadding,
      base 2 + 1 ≤ duration ∧ (Cantor.unpair (base 2)).2 + 1 ≤ nextDuration ∧
      graphSystem.Block (cfgAS 19 base rank 0 reserve)
        (((secondTopDuration rank (base 2) duration + 2) + nextDuration) +
          ((7*thirdFieldValue base+3) + (3*thirdFieldValue base+1)))
        (cfgFieldTransfer 79 (bankAS (thirdFieldBank base rank reserve padding count)
          (thirdFieldValue base) 0) 7 0
          ((bankAS (thirdFieldBank base rank reserve padding count) (thirdFieldValue base) 0) 7 +
            thirdFieldValue base)
          (((thirdFieldReserve base rank reserve padding nextPadding ++
            List.replicate (thirdFieldValue base) 0) ++ List.replicate (thirdFieldValue base) 0) ++
              List.replicate (thirdFieldValue base) 0))
        ((PASoundness.UnaryCodec.unary rank ++
          PASoundness.UnaryCodec.unary (Cantor.unpair (base 2)).1) ++
            PASoundness.UnaryCodec.unary (thirdFieldValue base)) := by
  obtain ⟨duration, padding, nextDuration, nextPadding, ht, hn, block⟩ :=
    rank_second_field_then_next_unpair rank count base reserve hc hcount
  have hs : bankOnlyCount (secondTopState base rank reserve padding).registers count 0 = 0 := by
    simp [bankOnlyCount, secondTopState, cfgFieldTransfer, bankFieldTransfer, bankAS]
  rw [unpair_exit_to_emit 68
    (bankOnlyCount (secondTopState base rank reserve padding).registers count)
    (Cantor.unpair (Cantor.unpair (base 2)).2).2
    (Cantor.unpair (Cantor.unpair (base 2)).2).1 0 _ hs] at block
  change graphSystem.Block (cfgAS 19 base rank 0 reserve) _
    (cfgAS 68 (thirdFieldBank base rank reserve padding count) (thirdFieldValue base) 0
      (thirdFieldReserve base rank reserve padding nextPadding)) _ at block
  have hem := emit_then_field_transfer (thirdFieldValue base) 68 7 "3.k.b.inc"
    emit_rows_68 field_transfer_rows_b (thirdFieldBank base rank reserve padding count)
    (thirdFieldReserve base rank reserve padding nextPadding)
  refine ⟨duration, padding, nextDuration, nextPadding, ht, hn, ?_⟩
  simpa using block.trans graphSystem hem

def thirdFieldDuration (base : RegisterMachine.Bank 9) (rank duration nextDuration : Nat) : Nat :=
  (secondTopDuration rank (base 2) duration + 2) + nextDuration +
    ((7*thirdFieldValue base+3) + (3*thirdFieldValue base+1))

def thirdFieldExit (base : RegisterMachine.Bank 9) (rank : Nat) (reserve : List Nat)
    (padding count nextPadding : Nat) : GraphState :=
  cfgFieldTransfer 79 (bankAS (thirdFieldBank base rank reserve padding count) (thirdFieldValue base) 0)
    7 0 ((bankAS (thirdFieldBank base rank reserve padding count) (thirdFieldValue base) 0) 7 +
      thirdFieldValue base)
    (((thirdFieldReserve base rank reserve padding nextPadding ++ List.replicate (thirdFieldValue base) 0) ++
      List.replicate (thirdFieldValue base) 0) ++ List.replicate (thirdFieldValue base) 0)

/-- Physical lift of the three-field positive-counter block, with an explicit
reachable-entry hypothesis. -/
theorem selected_rank_through_third_field (i rank count : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hc : base 8 = 0) (hcount : base 3 + rank = count+1)
    (h : graphSystem.run i = cfgAS 19 base rank 0 reserve) :
    ∃ duration padding nextDuration nextPadding finish,
      base 2 + 1 ≤ duration ∧ (Cantor.unpair (base 2)).2 + 1 ≤ nextDuration ∧ Good finish ∧
      finish.graphState = thirdFieldExit base rank reserve padding count nextPadding ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i + thirdFieldDuration base rank duration nextDuration)) ∧
      (machineWordSystem machine machineLabels).prefixWord
        (graphRefinement.boundary (i + thirdFieldDuration base rank duration nextDuration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++
          ((PASoundness.UnaryCodec.unary rank ++
            PASoundness.UnaryCodec.unary (Cantor.unpair (base 2)).1) ++
              PASoundness.UnaryCodec.unary (thirdFieldValue base)) ∧
      graphRefinement.boundary i <
        graphRefinement.boundary (i + thirdFieldDuration base rank duration nextDuration) := by
  obtain ⟨duration, padding, nextDuration, nextPadding, ht, hn, block⟩ :=
    rank_through_third_field rank count base reserve hc hcount
  change graphSystem.Block (cfgAS 19 base rank 0 reserve)
    (thirdFieldDuration base rank duration nextDuration)
    (thirdFieldExit base rank reserve padding count nextPadding) _ at block
  have hr := block.endpoint
  have hp := block.output
  obtain ⟨finish, hg, hs, hconfig⟩ := graphRefinement.related
    (i + thirdFieldDuration base rank duration nextDuration)
  refine ⟨duration, padding, nextDuration, nextPadding, finish, ht, hn, hg, ?_, hconfig, ?_, ?_⟩
  · rw [WordEventSystem.run_add, h, hr] at hs
    exact hs
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, WordEventSystem.prefix_add, h, hp]
  · apply graphRefinement.boundary_strict
    simp only [thirdFieldDuration, secondTopDuration]
    omega

end PASoundness.M236.OccurrenceGraph
