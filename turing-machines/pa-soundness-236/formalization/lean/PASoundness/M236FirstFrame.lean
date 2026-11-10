import PASoundness.M236CounterDispatch

/-! Final cleanup and zero result-bit emission for a zeroed work bank. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

def cfgExact (index : Nat) (bank : RegisterMachine.Bank 9) (reserve : List Nat) : GraphState :=
  ⟨index, bank, reserve⟩

def CleanupZero (bank : RegisterMachine.Bank 9) : Prop :=
  bank 6 = 0 ∧ bank 3 = 0 ∧ bank 2 = 0 ∧ bank 5 = 0 ∧ bank 7 = 0 ∧ bank 4 = 0

theorem cleanup_row724 : sourceRows[724]? = some ("3.k.a.decnz", 725, some 726) := by decide
theorem cleanup_row726 : sourceRows[726]? = some ("3.k.count.decnz", 727, some 749) := by decide
theorem cleanup_row749 : sourceRows[749]? = some ("3.k.rest.decnz", 750, some 751) := by decide
theorem cleanup_row751 : sourceRows[751]? = some ("3.k.env.decnz", 752, some 753) := by decide
theorem cleanup_row753 : sourceRows[753]? = some ("3.k.b.decnz", 754, some 755) := by decide
theorem cleanup_row755 : sourceRows[755]? = some ("3.k.top.decnz", 756, some 758) := by decide
theorem cleanup_row758 : sourceRows[758]? = some ("emit.0", 759, none) := by decide
theorem cleanup_row759 : sourceRows[759]? = some ("3.k.stage.inc", 0, none) := by decide

theorem cleanup_zero_a (bank : RegisterMachine.Bank 9) (reserve : List Nat) (h : bank 6 = 0) :
    graphSystem.step (cfgExact 724 bank reserve) = (cfgExact 726 bank reserve, []) := by
  simp [graphSystem, graphNext, cfgExact, cleanup_row724, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, RegisterMachine.execute, h]

theorem cleanup_zero_count (bank : RegisterMachine.Bank 9) (reserve : List Nat) (h : bank 3 = 0) :
    graphSystem.step (cfgExact 726 bank reserve) = (cfgExact 749 bank reserve, []) := by
  simp [graphSystem, graphNext, cfgExact, cleanup_row726, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, RegisterMachine.execute, h]

theorem cleanup_zero_rest (bank : RegisterMachine.Bank 9) (reserve : List Nat) (h : bank 2 = 0) :
    graphSystem.step (cfgExact 749 bank reserve) = (cfgExact 751 bank reserve, []) := by
  simp [graphSystem, graphNext, cfgExact, cleanup_row749, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, RegisterMachine.execute, h]

theorem cleanup_zero_env (bank : RegisterMachine.Bank 9) (reserve : List Nat) (h : bank 5 = 0) :
    graphSystem.step (cfgExact 751 bank reserve) = (cfgExact 753 bank reserve, []) := by
  simp [graphSystem, graphNext, cfgExact, cleanup_row751, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, RegisterMachine.execute, h]

theorem cleanup_zero_b (bank : RegisterMachine.Bank 9) (reserve : List Nat) (h : bank 7 = 0) :
    graphSystem.step (cfgExact 753 bank reserve) = (cfgExact 755 bank reserve, []) := by
  simp [graphSystem, graphNext, cfgExact, cleanup_row753, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, RegisterMachine.execute, h]

theorem cleanup_zero_top (bank : RegisterMachine.Bank 9) (reserve : List Nat) (h : bank 4 = 0) :
    graphSystem.step (cfgExact 755 bank reserve) = (cfgExact 758 bank reserve, []) := by
  simp [graphSystem, graphNext, cfgExact, cleanup_row755, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, RegisterMachine.execute, h]

theorem cleanup_emit_zero (bank : RegisterMachine.Bank 9) (reserve : List Nat) :
    graphSystem.step (cfgExact 758 bank reserve) = (cfgExact 759 bank reserve, [false]) := by
  simp [graphSystem, graphNext, cfgExact, cleanup_row758, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

theorem cleanup_next_stage (bank : RegisterMachine.Bank 9) (reserve : List Nat) :
    graphSystem.step (cfgExact 759 bank reserve) =
      (cfgExact 0 (RegisterMachine.write bank 1 (bank 1+1)) reserve, []) := by
  simp [graphSystem, graphNext, cfgExact, cleanup_row759, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, RegisterMachine.execute]

/-- A zeroed work bank emits zero and advances the stage in eight graph steps. -/
theorem cleanup_zero_frame (bank : RegisterMachine.Bank 9) (reserve : List Nat)
    (h : CleanupZero bank) :
    graphSystem.Block (cfgExact 724 bank reserve) 8
      (cfgExact 0 (RegisterMachine.write bank 1 (bank 1+1)) reserve) [false] := by
  rcases h with ⟨ha, hc, hr, he, hb, ht⟩
  have h1 := WordEventSystem.Block.single graphSystem (cleanup_zero_a bank reserve ha)
  have h2 := WordEventSystem.Block.single graphSystem (cleanup_zero_count bank reserve hc)
  have h3 := WordEventSystem.Block.single graphSystem (cleanup_zero_rest bank reserve hr)
  have h4 := WordEventSystem.Block.single graphSystem (cleanup_zero_env bank reserve he)
  have h5 := WordEventSystem.Block.single graphSystem (cleanup_zero_b bank reserve hb)
  have h6 := WordEventSystem.Block.single graphSystem (cleanup_zero_top bank reserve ht)
  have h7 := WordEventSystem.Block.single graphSystem (cleanup_emit_zero bank reserve)
  have h8 := WordEventSystem.Block.single graphSystem (cleanup_next_stage bank reserve)
  simpa using ((((((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4).trans graphSystem h5).trans graphSystem h6).trans graphSystem h7).trans graphSystem h8

def initialRankBank : RegisterMachine.Bank 9 := rankBase BlankFirst.zeros 0 1

def initialCleanupState (padding pad nextPad : Nat) : GraphState :=
  thirdCleanupState initialRankBank 1 (BlankFirst.reserve ++ List.replicate padding 0) pad nextPad

theorem initial_cleanup_bank_zero (padding pad nextPad : Nat) :
    CleanupZero (initialCleanupState padding pad nextPad).registers := by
  simp [CleanupZero, initialCleanupState, thirdCleanupState, cfgCountTop, bankCountTop,
    thirdFieldExit, cfgFieldTransfer, bankFieldTransfer, bankAS, thirdFieldBank, bankAC, bankRest,
    bankOnlyCount, secondTopState, secondDecodedBank, secondFieldBase, bankCountA,
    initialRankBank, rankBase, BlankFirst.zeros, thirdFieldValue, Cantor.unpair, Cantor.unpairAux]

theorem initial_cleanup_stage_zero (padding pad nextPad : Nat) :
    (initialCleanupState padding pad nextPad).registers 1 = 0 := by
  simp [initialCleanupState, thirdCleanupState, cfgCountTop, bankCountTop,
    thirdFieldExit, cfgFieldTransfer, bankFieldTransfer, bankAS, thirdFieldBank, bankAC, bankRest,
    bankOnlyCount, secondTopState, secondDecodedBank, secondFieldBase, bankCountA,
    initialRankBank, rankBase, BlankFirst.zeros, thirdFieldValue, Cantor.unpair, Cantor.unpairAux]

theorem initial_cleanup_bank_all_zero (padding pad nextPad : Nat) :
    (initialCleanupState padding pad nextPad).registers = BlankFirst.zeros := by
  have hz := initial_cleanup_bank_zero padding pad nextPad
  rcases hz with ⟨h6, h3, h2, h5, h7, h4⟩
  have h1 := initial_cleanup_stage_zero padding pad nextPad
  have h0 : (initialCleanupState padding pad nextPad).registers 0 = 0 := by
    simp [initialCleanupState, thirdCleanupState, cfgCountTop, bankCountTop,
      thirdFieldExit, cfgFieldTransfer, bankFieldTransfer, bankAS]
  have h8 : (initialCleanupState padding pad nextPad).registers 8 = 0 := by
    simp [initialCleanupState, thirdCleanupState, cfgCountTop, bankCountTop,
      thirdFieldExit, cfgFieldTransfer, bankFieldTransfer, bankAS, thirdFieldBank, bankAC]
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8

/-- The literal blank-start machine emits one syntactically complete unary
frame for address `(1, 0, [0])` and bit zero, then reaches the stage-one graph
boundary. This finite theorem does not identify the producer's value function. -/
theorem initial_frame_on_selected :
    ∃ i finish reserve, Good finish ∧ graphSystem.run i = cfg 0 BlankFirst.zeros 1 0 0 reserve ∧
      finish.graphState = cfg 0 BlankFirst.zeros 1 0 0 reserve ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run (graphRefinement.boundary i) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) =
        PASoundness.UnaryCodec.encodeFrame ⟨1, 0, [0]⟩ false := by
  obtain ⟨before, padding, _, scan⟩ := unpair_to_rank_entry 0 BlankFirst.zeros BlankFirst.reserve
  have hgraph : graphSystem.run (2 + before) =
      cfgAS 19 initialRankBank 1 0 (BlankFirst.reserve ++ List.replicate padding 0) := by
    rw [WordEventSystem.run_add, initial_diagonal_entry, scan.endpoint]
    simpa [initialRankBank, Cantor.unpair, Cantor.unpairAux] using
      rank_entry_convert BlankFirst.zeros 0 1 (BlankFirst.reserve ++ List.replicate padding 0) rfl
  have hp2 : graphSystem.prefixWord 2 = [] := by
    have hg := (copy_at_graph_run 0 0 BlankFirst.zeros 0 BlankFirst.reserve initial_copy_entry).2
    simpa using hg
  have hp : graphSystem.prefixWord (2 + before) = [] := by
    rw [WordEventSystem.prefix_add, initial_diagonal_entry, scan.output, hp2, List.append_nil]
  have hc : initialRankBank 8 = 0 := by simp [initialRankBank, rankBase, bankAC]
  have hcount : initialRankBank 3 + 1 = 1 := by
    simp [initialRankBank, rankBase, bankAC, bankRest, BlankFirst.zeros]
  obtain ⟨duration, pad, nextDuration, nextPad, _, _, block⟩ :=
    rank_third_field_zero_cleanup 1 initialRankBank (BlankFirst.reserve ++ List.replicate padding 0) hc hcount
  let elapsed := thirdCleanupDuration initialRankBank 1 (BlankFirst.reserve ++ List.replicate padding 0)
    duration pad nextDuration nextPad
  let state := initialCleanupState padding pad nextPad
  change graphSystem.Block (cfgAS 19 initialRankBank 1 0 (BlankFirst.reserve ++ List.replicate padding 0))
    elapsed state _ at block
  have hr : graphSystem.run ((2+before) + elapsed) = state := by
    rw [WordEventSystem.run_add, hgraph, block.endpoint]
  have hw : graphSystem.prefixWord ((2+before) + elapsed) = [true, false, false, false] := by
    rw [WordEventSystem.prefix_add, hgraph, block.output, hp]
    simp [initialRankBank, rankBase, bankAC, bankRest, BlankFirst.zeros,
      thirdFieldValue, Cantor.unpair, Cantor.unpairAux, PASoundness.UnaryCodec.unary]
  have heq : state = cfgExact 724 state.registers state.reserve := rfl
  have hfinish := cleanup_zero_frame state.registers state.reserve (initial_cleanup_bank_zero padding pad nextPad)
  have hr' : graphSystem.run (((2+before) + elapsed) + 8) =
      cfgExact 0 (RegisterMachine.write state.registers 1 (state.registers 1+1)) state.reserve := by
    rw [WordEventSystem.run_add, hr, heq, hfinish.endpoint]
    rfl
  have hw' : graphSystem.prefixWord (((2+before) + elapsed) + 8) = [true, false, false, false, false] := by
    rw [WordEventSystem.prefix_add, hr, heq, hfinish.output, hw]
    rfl
  obtain ⟨finish, hg, hs, hconfig⟩ := graphRefinement.related (((2+before) + elapsed) + 8)
  rw [hr'] at hs
  have hb : RegisterMachine.write state.registers 1 (state.registers 1+1) =
      bankWith BlankFirst.zeros 1 0 0 := by
    rw [show state.registers = BlankFirst.zeros from initial_cleanup_bank_all_zero padding pad nextPad]
    funext j
    fin_cases j <;> simp [RegisterMachine.write, bankWith, BlankFirst.zeros]
  have hfinal : cfgExact 0 (RegisterMachine.write state.registers 1 (state.registers 1+1)) state.reserve =
      cfg 0 BlankFirst.zeros 1 0 0 state.reserve := congrArg (fun b => cfgExact 0 b state.reserve) hb
  refine ⟨((2+before) + elapsed) + 8, finish, state.reserve, hg, hr'.trans hfinal,
    hs.trans hfinal, hconfig, ?_⟩
  rw [graphRefinement.prefix_eq, hw']
  rfl

end PASoundness.M236.OccurrenceGraph
