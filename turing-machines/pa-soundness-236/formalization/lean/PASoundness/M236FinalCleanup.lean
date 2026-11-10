import PASoundness.M236ResidualCoordinates

/-! Exact final cleanup for an arbitrary prepared entry at graph row 749. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

def finalBank (base : RegisterMachine.Bank 9) (rest env b top : Nat) : RegisterMachine.Bank 9 :=
  fun i => if i = 2 then rest else if i = 5 then env else if i = 7 then b else if i = 4 then top else base i

def finalCfg (index : Nat) (base : RegisterMachine.Bank 9) (rest env b top : Nat)
    (reserve : List Nat) : GraphState := ⟨index, finalBank base rest env b top, reserve⟩

theorem final_row750 : sourceRows[750]? = some ("jump", 749, none) := by decide
theorem final_row752 : sourceRows[752]? = some ("jump", 751, none) := by decide
theorem final_row754 : sourceRows[754]? = some ("jump", 753, none) := by decide
theorem final_row756 : sourceRows[756]? = some ("emit.1", 757, none) := by decide
theorem final_row757 : sourceRows[757]? = some ("jump", 755, none) := by decide

theorem final_dec_rest (base : RegisterMachine.Bank 9) (rest env b top : Nat) (reserve : List Nat) :
    graphSystem.step (finalCfg 749 base (rest+1) env b top reserve) =
      (finalCfg 750 base rest env b top (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, finalCfg, cleanup_row749, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, finalBank, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [finalBank, RegisterMachine.write])

theorem final_zero_rest (base : RegisterMachine.Bank 9) (env b top : Nat) (reserve : List Nat) :
    graphSystem.step (finalCfg 749 base 0 env b top reserve) = (finalCfg 751 base 0 env b top reserve, []) := by
  simp [graphSystem, graphNext, finalCfg, cleanup_row749, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, finalBank, RegisterMachine.execute, RegisterMachine.write]

theorem final_jump_rest (base : RegisterMachine.Bank 9) (rest env b top : Nat) (reserve : List Nat) :
    graphSystem.step (finalCfg 750 base rest env b top reserve) = (finalCfg 749 base rest env b top reserve, []) := by
  simp [graphSystem, graphNext, finalCfg, final_row750, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

theorem final_dec_env (base : RegisterMachine.Bank 9) (rest env b top : Nat) (reserve : List Nat) :
    graphSystem.step (finalCfg 751 base rest (env+1) b top reserve) =
      (finalCfg 752 base rest env b top (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, finalCfg, cleanup_row751, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, finalBank, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [finalBank, RegisterMachine.write])

theorem final_zero_env (base : RegisterMachine.Bank 9) (rest b top : Nat) (reserve : List Nat) :
    graphSystem.step (finalCfg 751 base rest 0 b top reserve) = (finalCfg 753 base rest 0 b top reserve, []) := by
  simp [graphSystem, graphNext, finalCfg, cleanup_row751, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, finalBank, RegisterMachine.execute, RegisterMachine.write]

theorem final_jump_env (base : RegisterMachine.Bank 9) (rest env b top : Nat) (reserve : List Nat) :
    graphSystem.step (finalCfg 752 base rest env b top reserve) = (finalCfg 751 base rest env b top reserve, []) := by
  simp [graphSystem, graphNext, finalCfg, final_row752, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

theorem final_dec_b (base : RegisterMachine.Bank 9) (rest env b top : Nat) (reserve : List Nat) :
    graphSystem.step (finalCfg 753 base rest env (b+1) top reserve) =
      (finalCfg 754 base rest env b top (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, finalCfg, cleanup_row753, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, finalBank, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [finalBank, RegisterMachine.write])

theorem final_zero_b (base : RegisterMachine.Bank 9) (rest env top : Nat) (reserve : List Nat) :
    graphSystem.step (finalCfg 753 base rest env 0 top reserve) = (finalCfg 755 base rest env 0 top reserve, []) := by
  simp [graphSystem, graphNext, finalCfg, cleanup_row753, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, finalBank, RegisterMachine.execute, RegisterMachine.write]

theorem final_jump_b (base : RegisterMachine.Bank 9) (rest env b top : Nat) (reserve : List Nat) :
    graphSystem.step (finalCfg 754 base rest env b top reserve) = (finalCfg 753 base rest env b top reserve, []) := by
  simp [graphSystem, graphNext, finalCfg, final_row754, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

theorem final_drain_rest (rest : Nat) (base : RegisterMachine.Bank 9) (env b top : Nat) (reserve : List Nat) :
    graphSystem.Block (finalCfg 749 base rest env b top reserve) (2*rest+1)
      (finalCfg 751 base 0 env b top (reserve ++ List.replicate rest 0)) [] := by
  induction rest generalizing reserve with
  | zero => simpa using WordEventSystem.Block.single graphSystem (final_zero_rest base env b top reserve)
  | succ rest ih =>
    have h1 := WordEventSystem.Block.single graphSystem (final_dec_rest base rest env b top reserve)
    have h2 := WordEventSystem.Block.single graphSystem (final_jump_rest base rest env b top (reserve ++ [0]))
    have h := (h1.trans graphSystem h2).trans graphSystem (ih (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem final_drain_env (env : Nat) (base : RegisterMachine.Bank 9) (rest b top : Nat) (reserve : List Nat) :
    graphSystem.Block (finalCfg 751 base rest env b top reserve) (2*env+1)
      (finalCfg 753 base rest 0 b top (reserve ++ List.replicate env 0)) [] := by
  induction env generalizing reserve with
  | zero => simpa using WordEventSystem.Block.single graphSystem (final_zero_env base rest b top reserve)
  | succ env ih =>
    have h1 := WordEventSystem.Block.single graphSystem (final_dec_env base rest env b top reserve)
    have h2 := WordEventSystem.Block.single graphSystem (final_jump_env base rest env b top (reserve ++ [0]))
    have h := (h1.trans graphSystem h2).trans graphSystem (ih (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem final_drain_b (b : Nat) (base : RegisterMachine.Bank 9) (rest env top : Nat) (reserve : List Nat) :
    graphSystem.Block (finalCfg 753 base rest env b top reserve) (2*b+1)
      (finalCfg 755 base rest env 0 top (reserve ++ List.replicate b 0)) [] := by
  induction b generalizing reserve with
  | zero => simpa using WordEventSystem.Block.single graphSystem (final_zero_b base rest env top reserve)
  | succ b ih =>
    have h1 := WordEventSystem.Block.single graphSystem (final_dec_b base rest env b top reserve)
    have h2 := WordEventSystem.Block.single graphSystem (final_jump_b base rest env b top (reserve ++ [0]))
    have h := (h1.trans graphSystem h2).trans graphSystem (ih (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem final_dec_top (base : RegisterMachine.Bank 9) (rest env b top : Nat) (reserve : List Nat) :
    graphSystem.step (finalCfg 755 base rest env b (top+1) reserve) =
      (finalCfg 756 base rest env b top (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, finalCfg, cleanup_row755, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, finalBank, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [finalBank, RegisterMachine.write])

theorem final_zero_top (base : RegisterMachine.Bank 9) (rest env b : Nat) (reserve : List Nat) :
    graphSystem.step (finalCfg 755 base rest env b 0 reserve) = (finalCfg 758 base rest env b 0 reserve, []) := by
  simp [graphSystem, graphNext, finalCfg, cleanup_row755, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, finalBank, RegisterMachine.execute, RegisterMachine.write]

theorem final_emit_one (base : RegisterMachine.Bank 9) (rest env b top : Nat) (reserve : List Nat) :
    graphSystem.step (finalCfg 756 base rest env b top reserve) = (finalCfg 757 base rest env b top reserve, [true]) := by
  simp [graphSystem, graphNext, finalCfg, final_row756, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

theorem final_jump_top (base : RegisterMachine.Bank 9) (rest env b top : Nat) (reserve : List Nat) :
    graphSystem.step (finalCfg 757 base rest env b top reserve) = (finalCfg 755 base rest env b top reserve, []) := by
  simp [graphSystem, graphNext, finalCfg, final_row757, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

theorem final_drain_top (top : Nat) (base : RegisterMachine.Bank 9) (rest env b : Nat) (reserve : List Nat) :
    graphSystem.Block (finalCfg 755 base rest env b top reserve) (3*top+1)
      (finalCfg 758 base rest env b 0 (reserve ++ List.replicate top 0)) (List.replicate top true) := by
  induction top generalizing reserve with
  | zero => simpa using WordEventSystem.Block.single graphSystem (final_zero_top base rest env b reserve)
  | succ top ih =>
    have h1 := WordEventSystem.Block.single graphSystem (final_dec_top base rest env b top reserve)
    have h2 := WordEventSystem.Block.single graphSystem (final_emit_one base rest env b top (reserve ++ [0]))
    have h3 := WordEventSystem.Block.single graphSystem (final_jump_top base rest env b top (reserve ++ [0]))
    have h := ((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem (ih (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

/-- From an arbitrary prepared cleanup bank, rows 749--759 clear `rest`,
`env`, `b` and `top`, emit `top` one-bits followed by zero, and increment
the stage. Other registers are preserved. This is a valid Boolean field only
when the initial `top` is at most one. -/
theorem final_cleanup (base : RegisterMachine.Bank 9) (rest env b top : Nat) (reserve : List Nat) :
    graphSystem.Block (finalCfg 749 base rest env b top reserve) (2*(rest+env+b)+3*top+6)
      (cfgExact 0 (RegisterMachine.write (finalBank base 0 0 0 0) 1 (base 1+1))
        (reserve ++ List.replicate (rest+env+b+top) 0))
      (List.replicate top true ++ [false]) := by
  have h1 := final_drain_rest rest base env b top reserve
  have h2 := final_drain_env env base 0 b top (reserve ++ List.replicate rest 0)
  have h3 := final_drain_b b base 0 0 top ((reserve ++ List.replicate rest 0) ++ List.replicate env 0)
  have h4 := final_drain_top top base 0 0 0 (((reserve ++ List.replicate rest 0) ++ List.replicate env 0) ++ List.replicate b 0)
  have h5 := WordEventSystem.Block.single graphSystem
    (cleanup_emit_zero (finalBank base 0 0 0 0)
      ((((reserve ++ List.replicate rest 0) ++ List.replicate env 0) ++ List.replicate b 0) ++ List.replicate top 0))
  have h6 := WordEventSystem.Block.single graphSystem
    (cleanup_next_stage (finalBank base 0 0 0 0)
      ((((reserve ++ List.replicate rest 0) ++ List.replicate env 0) ++ List.replicate b 0) ++ List.replicate top 0))
  have h := ((((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4).trans graphSystem h5).trans graphSystem h6
  have hres : ((((reserve ++ List.replicate rest 0) ++ List.replicate env 0) ++ List.replicate b 0) ++ List.replicate top 0) =
      reserve ++ List.replicate (rest+env+b+top) 0 := by
    simp only [List.replicate_add, List.append_assoc]
  rw [hres] at h
  have htime : (((((2*rest+1)+(2*env+1))+(2*b+1))+(3*top+1))+1)+1 = 2*(rest+env+b)+3*top+6 := by omega
  rw [htime] at h
  simpa [finalCfg, cfgExact, finalBank, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem final_cfg_view (index : Nat) (bank : RegisterMachine.Bank 9) (reserve : List Nat) :
    cfgExact index bank reserve = finalCfg index bank (bank 2) (bank 5) (bank 7) (bank 4) reserve := by
  unfold cfgExact finalCfg
  congr 1
  funext i
  fin_cases i <;> simp [finalBank]

/-- When all non-cleared work registers and `top` are zero, cleanup emits a
single zero bit and returns to a completely clean scheduler bank. The input
`rest`, `env` and `b` remain arbitrary. -/
theorem final_cleanup_clean (bank : RegisterMachine.Bank 9) (reserve : List Nat)
    (h0 : bank 0 = 0) (h3 : bank 3 = 0) (h4 : bank 4 = 0)
    (h6 : bank 6 = 0) (h8 : bank 8 = 0) :
    graphSystem.Block (cfgExact 749 bank reserve) (2*(bank 2+bank 5+bank 7)+6)
      (cfg 0 BlankFirst.zeros (bank 1+1) 0 0
        (reserve ++ List.replicate (bank 2+bank 5+bank 7) 0)) [false] := by
  have h := final_cleanup bank (bank 2) (bank 5) (bank 7) (bank 4) reserve
  rw [← final_cfg_view 749 bank reserve] at h
  have hbank : RegisterMachine.write (finalBank bank 0 0 0 0) 1 (bank 1+1) =
      bankWith BlankFirst.zeros (bank 1+1) 0 0 := by
    funext i
    fin_cases i <;> simp [finalBank, RegisterMachine.write, bankWith, BlankFirst.zeros, h0, h3, h6, h8]
  rw [hbank, h4] at h
  simpa [cfg, cfgExact] using h

/-- The clean-output cleanup also holds on the literal selected run whenever
the prepared graph entry is actually reached. -/
theorem selected_final_cleanup_clean (i : Nat) (bank : RegisterMachine.Bank 9) (reserve : List Nat)
    (h0 : bank 0 = 0) (h3 : bank 3 = 0) (h4 : bank 4 = 0)
    (h6 : bank 6 = 0) (h8 : bank 8 = 0)
    (h : graphSystem.run i = cfgExact 749 bank reserve) :
    ∃ finish, Good finish ∧
      finish.graphState = cfg 0 BlankFirst.zeros (bank 1+1) 0 0
        (reserve ++ List.replicate (bank 2+bank 5+bank 7) 0) ∧
      graphSystem.run (i + (2*(bank 2+bank 5+bank 7)+6)) =
        cfg 0 BlankFirst.zeros (bank 1+1) 0 0 (reserve ++ List.replicate (bank 2+bank 5+bank 7) 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i + (2*(bank 2+bank 5+bank 7)+6))) ∧
      (machineWordSystem machine machineLabels).prefixWord
          (graphRefinement.boundary (i + (2*(bank 2+bank 5+bank 7)+6))) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++ [false] ∧
      graphRefinement.boundary i < graphRefinement.boundary (i + (2*(bank 2+bank 5+bank 7)+6)) := by
  have block := final_cleanup_clean bank reserve h0 h3 h4 h6 h8
  have hr : graphSystem.run (i + (2*(bank 2+bank 5+bank 7)+6)) =
      cfg 0 BlankFirst.zeros (bank 1+1) 0 0 (reserve ++ List.replicate (bank 2+bank 5+bank 7) 0) := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i + (2*(bank 2+bank 5+bank 7)+6)) = graphSystem.prefixWord i ++ [false] := by
    rw [WordEventSystem.prefix_add, h, block.output]
  obtain ⟨finish, hg, hs, hc⟩ := graphRefinement.related (i + (2*(bank 2+bank 5+bank 7)+6))
  refine ⟨finish, hg, hs.trans hr, hr, hc, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

/-- Residual fields and a false result bit, followed by a clean next-stage
boundary. The base stage, residual packed input, and `env`/`b` values are
arbitrary; zero scratch and zero `top` are explicit hypotheses. -/
theorem residual_coordinates_false_frame (n : Nat) (base : RegisterMachine.Bank 9) (rest : Nat)
    (reserve : List Nat) (h0 : base 0 = 0) (h4 : base 4 = 0) :
    ∃ duration padding, n+7 ≤ duration ∧
      graphSystem.Block (cfgRAC 726 (bankOnlyCount base n) rest 0 0 reserve) duration
        (cfg 0 BlankFirst.zeros (base 1+1) 0 0 (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.encodeFields (Schedule.decodeCoordinates n rest) ++ [false]) := by
  obtain ⟨duration, padding, hd, hresidual⟩ := residual_coordinates_finish n base rest reserve h0
  let bank := bankAC (bankRest (bankOnlyCount base 0) (residualTail n rest)) 0 0
  have hb0 : bank 0 = 0 := by simp [bank, bankAC, bankRest, bankOnlyCount, h0]
  have hb3 : bank 3 = 0 := by simp [bank, bankAC, bankRest, bankOnlyCount]
  have hb4 : bank 4 = 0 := by simp [bank, bankAC, bankRest, bankOnlyCount, h4]
  have hb6 : bank 6 = 0 := by simp [bank, bankAC, bankRest, bankOnlyCount]
  have hb8 : bank 8 = 0 := by simp [bank, bankAC, bankRest, bankOnlyCount]
  have hb1 : bank 1 = base 1 := by simp [bank, bankAC, bankRest, bankOnlyCount]
  have hclean := final_cleanup_clean bank (reserve ++ List.replicate padding 0) hb0 hb3 hb4 hb6 hb8
  have hentry : cfgRAC 749 (bankOnlyCount base 0) (residualTail n rest) 0 0
      (reserve ++ List.replicate padding 0) = cfgExact 749 bank (reserve ++ List.replicate padding 0) := rfl
  rw [hentry] at hresidual
  have h := hresidual.trans graphSystem hclean
  refine ⟨duration + (2*(bank 2+bank 5+bank 7)+6), padding + (bank 2+bank 5+bank 7), by omega, ?_⟩
  have hreserve : (reserve ++ List.replicate padding 0) ++ List.replicate (bank 2+bank 5+bank 7) 0 =
      reserve ++ List.replicate (padding + (bank 2+bank 5+bank 7)) 0 := by
    simp only [List.replicate_add, List.append_assoc]
  rw [hreserve, hb1] at h
  exact h

end PASoundness.M236.OccurrenceGraph
