import PASoundness.M236SignedNonatomic

/-! Finite prepared non-atomic walks between the two checked graph phases. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

/-- The canonical loop-boundary bank retains the stage, remainder, counter,
formula and environment; all four work registers are zero. -/
def signedWalkBank (stage count rest env formula : Nat) : RegisterMachine.Bank 9 :=
  fun i => if i = 1 then stage else if i = 2 then rest else if i = 3 then count
    else if i = 4 then formula else if i = 5 then env else 0

def signedWalkIndex (phase : Bool) : Nat := if phase then 546 else 366

def signedWalkCfg (phase : Bool) (stage count rest env formula : Nat) (reserve : List Nat) : GraphState :=
  cfgExact (signedWalkIndex phase) (signedWalkBank stage count rest env formula) reserve

structure SignedMoveRows (k : Nat) : Prop where
  decTop : sourceRows[k]? = some ("3.k.top.decnz", k+1, some (k+3))
  incB : sourceRows[k+1]? = some ("3.k.b.inc", k+2, none)
  jump : sourceRows[k+2]? = some ("jump", k, none)

theorem signed_move_rows_366 : SignedMoveRows 366 := by constructor <;> decide
theorem signed_move_rows_546 : SignedMoveRows 546 := by constructor <;> decide

theorem signed_move_dec (k : Nat) (rows : SignedMoveRows k) (base : RegisterMachine.Bank 9)
    (b top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgTimeout k base b (top+1) reserve) =
      (cfgTimeout (k+1) base b top (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgTimeout, rows.decTop, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, timeoutBank, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [timeoutBank, RegisterMachine.write])

theorem signed_move_zero (k : Nat) (rows : SignedMoveRows k) (base : RegisterMachine.Bank 9)
    (b : Nat) (reserve : List Nat) :
    graphSystem.step (cfgTimeout k base b 0 reserve) = (cfgTimeout (k+3) base b 0 reserve, []) := by
  simp [graphSystem, graphNext, cfgTimeout, rows.decTop, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, timeoutBank, RegisterMachine.execute]

theorem signed_move_inc (k : Nat) (rows : SignedMoveRows k) (base : RegisterMachine.Bank 9)
    (b top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgTimeout (k+1) base b top reserve) = (cfgTimeout (k+2) base (b+1) top reserve, []) := by
  simp [graphSystem, graphNext, cfgTimeout, rows.incB, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, timeoutBank, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [timeoutBank, RegisterMachine.write])

theorem signed_move_jump (k : Nat) (rows : SignedMoveRows k) (base : RegisterMachine.Bank 9)
    (b top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgTimeout (k+2) base b top reserve) = (cfgTimeout k base b top reserve, []) := by
  simp [graphSystem, graphNext, cfgTimeout, rows.jump, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

/-- Move the whole arbitrary top register into b, with exact time, silent word
and one added zero reserve block per unit. -/
theorem signed_move_all (n k : Nat) (rows : SignedMoveRows k) (base : RegisterMachine.Bank 9)
    (b : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgTimeout k base b n reserve) (3*n+1)
      (cfgTimeout (k+3) base (b+n) 0 (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing b reserve with
  | zero => simpa using WordEventSystem.Block.single graphSystem (signed_move_zero k rows base b reserve)
  | succ n ih =>
    have h1 := WordEventSystem.Block.single graphSystem (signed_move_dec k rows base b n reserve)
    have h2 := WordEventSystem.Block.single graphSystem (signed_move_inc k rows base b n (reserve ++ [0]))
    have h3 := WordEventSystem.Block.single graphSystem (signed_move_jump k rows base (b+1) n (reserve ++ [0]))
    have h := ((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem (ih (b+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem signed_row723 : sourceRows[723]? = some ("jump", 366, none) := by decide

theorem signed_jump723 (bank : RegisterMachine.Bank 9) (reserve : List Nat) :
    graphSystem.step (cfgExact 723 bank reserve) = (cfgExact 366 bank reserve, []) := by
  simp [graphSystem, graphNext, cfgExact, signed_row723, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

theorem signed_walk_entry_view (i stage count rest env formula : Nat) (reserve : List Nat) :
    cfgExact i (signedWalkBank stage count rest env formula) reserve =
      cfgTimeout i (signedWalkBank stage count rest env formula) 0 formula reserve := by
  unfold cfgExact cfgTimeout
  congr 1
  funext j
  fin_cases j <;> simp [signedWalkBank, timeoutBank]

/-- One prepared non-atomic graph step from a checked top-to-b occurrence to
its checked continuation, retaining arbitrary packed remainder. -/
theorem signed_walk_core (start dest : Nat) (mr : SignedMoveRows start)
    (dr : CounterDispatchRows (start+3)) (ur : UnpairRows (start+3+5))
    (er : EmitRows (start+3+5+11))
    (scan : FormulaScanRows (start+3+24)) (branch : FormulaBranchRow (start+3+24))
    (select : ChildSelectRows (start+3+24+9)) (pairRows : PairEnvRows (start+3+24+9+12))
    (next : ChildNextRow (start+3+24+9) dest)
    (stage count rest env formula : Nat) (reserve : List Nat)
    (htag : (Cantor.unpair formula).1 ≠ 0) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block (cfgExact start (signedWalkBank stage (count+1) rest env formula) reserve) duration
        (cfgExact dest (signedWalkBank stage count (Cantor.unpair rest).2
          (Cantor.pair ((Cantor.unpair rest).1-1) env) (M236Game.child formula (Cantor.unpair rest).1))
          (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.unary (Cantor.unpair rest).1) := by
  let W := signedWalkBank stage (count+1) rest env formula
  let T := timeoutBank W formula 0
  have he := signed_walk_entry_view start stage (count+1) rest env formula reserve
  have h1 := signed_move_all formula start mr W 0 reserve
  simp only [Nat.zero_add] at h1
  rw [← he] at h1
  rw [timeout_count_view (start+3) W formula 0 _, show W 3 = count+1 by simp [W, signedWalkBank]] at h1
  have hs : T 0 = 0 := by simp [T, W, timeoutBank, signedWalkBank]
  have ha : T 6 = 0 := by simp [T, W, timeoutBank, signedWalkBank]
  have hc : T 8 = 0 := by simp [T, W, timeoutBank, signedWalkBank]
  have hf : T 7 = formula := by simp [T, timeoutBank]
  have hr : T 2 = rest := by simp [T, W, timeoutBank, signedWalkBank]
  have hen : T 5 = env := by simp [T, W, timeoutBank, signedWalkBank]
  have hs' : (Cantor.unpair (T 7)).1 ≠ 0 := by simpa [hf] using htag
  obtain ⟨d1, p1, d2, p2, hd1, hd2, h2⟩ := signed_coordinate_nonatomic_step (start+3) dest
    dr ur er scan branch select pairRows next T count (reserve ++ List.replicate formula 0) hs ha hc hs'
  have hstate : cfgBudget dest
      (bankSelect (signedCoordinateBank T count) ((Cantor.unpair (T 2)).1-1) 0 0 0
        (M236Game.child (T 7) (Cantor.unpair (T 2)).1))
      count (Cantor.pair ((Cantor.unpair (T 2)).1-1) (T 5)) 0 0
      (signedCoordinateReserve T (reserve ++ List.replicate formula 0) p1 ++ List.replicate p2 0) =
      cfgExact dest (signedWalkBank stage count (Cantor.unpair rest).2
        (Cantor.pair ((Cantor.unpair rest).1-1) env) (M236Game.child formula (Cantor.unpair rest).1))
        (signedCoordinateReserve T (reserve ++ List.replicate formula 0) p1 ++ List.replicate p2 0) := by
    unfold cfgBudget cfgExact
    congr 1
    funext j
    fin_cases j <;> simp [signedCoordinateBank, bankSelect, bankHalf, bankAC, bankRest,
      bankCountTop, bankBudget, RegisterMachine.write, T, W, timeoutBank, signedWalkBank]
  rw [hstate] at h2
  have h := h1.trans graphSystem h2
  refine ⟨(3*formula+1)+((2+(d1+(7*(Cantor.unpair rest).1+3)))+d2),
    formula+1+p1+(Cantor.unpair rest).1+(Cantor.unpair rest).1+p2, by omega, ?_⟩
  have hreserve : signedCoordinateReserve T (reserve ++ List.replicate formula 0) p1 ++ List.replicate p2 0 =
      reserve ++ List.replicate (formula+1+p1+(Cantor.unpair rest).1+(Cantor.unpair rest).1+p2) 0 := by
    simp only [signedCoordinateReserve, hr]
    change (((((reserve ++ List.replicate formula 0) ++ List.replicate 1 0) ++ List.replicate p1 0) ++
      List.replicate (Cantor.unpair rest).1 0) ++ List.replicate (Cantor.unpair rest).1 0) ++ List.replicate p2 0 = _
    simp only [List.append_assoc, ← List.replicate_add]
  rw [hreserve] at h
  simpa [hr] using h

/-- A non-atomic step toggles between the two canonical graph phases, emits
one coordinate, decrements the counter, and updates formula and environment. -/
theorem signed_walk_step (phase : Bool) (stage count rest env formula : Nat) (reserve : List Nat)
    (htag : (Cantor.unpair formula).1 ≠ 0) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block (signedWalkCfg phase stage (count+1) rest env formula reserve) duration
        (signedWalkCfg (!phase) stage count (Cantor.unpair rest).2
          (Cantor.pair ((Cantor.unpair rest).1-1) env) (M236Game.child formula (Cantor.unpair rest).1)
          (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.unary (Cantor.unpair rest).1) := by
  cases phase with
  | false =>
    obtain ⟨duration, padding, ht, block⟩ := signed_walk_core 366 546 signed_move_rows_366
      timeout_rows_369 positive_unpair_rows_374 positive_emit_rows_385 formula_scan_rows_393 formula_branch_row_393
      child_rows_402 pair_env_rows_414 child_next_402 stage count rest env formula reserve htag
    exact ⟨duration, padding, ht, by simpa [signedWalkCfg, signedWalkIndex] using block⟩
  | true =>
    obtain ⟨duration, padding, ht, block⟩ := signed_walk_core 546 723 signed_move_rows_546
      signed_dispatch_rows_549 signed_unpair_rows_554 signed_emit_rows_565 formula_scan_rows_573 formula_branch_row_573
      child_rows_582 pair_env_rows_594 child_next_582 stage count rest env formula reserve htag
    have jump := WordEventSystem.Block.single graphSystem
      (signed_jump723 (signedWalkBank stage count (Cantor.unpair rest).2
        (Cantor.pair ((Cantor.unpair rest).1-1) env) (M236Game.child formula (Cantor.unpair rest).1))
        (reserve ++ List.replicate padding 0))
    exact ⟨duration+1, padding, by omega, by simpa [signedWalkCfg, signedWalkIndex] using block.trans graphSystem jump⟩

/-- Require a nonzero tag only at formulas whose moves are actually consumed. -/
def NonatomicMoves : Nat → List Nat → Prop
  | _, [] => True
  | formula, move :: moves => (Cantor.unpair formula).1 ≠ 0 ∧ NonatomicMoves (M236Game.child formula move) moves

def signedMovesFormula : Nat → List Nat → Nat
  | formula, [] => formula
  | formula, move :: moves => signedMovesFormula (M236Game.child formula move) moves

def signedMovesEnvironment : Nat → List Nat → Nat
  | env, [] => env
  | env, move :: moves => signedMovesEnvironment (Cantor.pair (move-1) env) moves

def signedMovesPhase : Bool → List Nat → Bool
  | phase, [] => phase
  | phase, _ :: moves => signedMovesPhase (!phase) moves

/-- Any finite list of non-atomic moves is realized by adjacent graph segments.
The counter has the explicit spare budget `remaining`, the packed tail is
arbitrary, and only the consumed formulas require nonzero tags. -/
theorem signed_walk_moves (moves : List Nat) (phase : Bool) (stage remaining tail env formula : Nat)
    (reserve : List Nat) (hnonatomic : NonatomicMoves formula moves) :
    ∃ duration padding, moves.length ≤ duration ∧
      graphSystem.Block
        (signedWalkCfg phase stage (remaining+moves.length) (Schedule.packCoordinates moves tail) env formula reserve) duration
        (signedWalkCfg (signedMovesPhase phase moves) stage remaining tail
          (signedMovesEnvironment env moves) (signedMovesFormula formula moves)
          (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.encodeFields moves) := by
  induction moves generalizing phase env formula reserve with
  | nil =>
    refine ⟨0, 0, by simp, ?_⟩
    simpa [Schedule.packCoordinates, signedMovesPhase, signedMovesEnvironment, signedMovesFormula,
      PASoundness.UnaryCodec.encodeFields] using
      WordEventSystem.Block.refl graphSystem (signedWalkCfg phase stage remaining tail env formula reserve)
  | cons move moves ih =>
    have htag : (Cantor.unpair formula).1 ≠ 0 := hnonatomic.1
    have htail : NonatomicMoves (M236Game.child formula move) moves := hnonatomic.2
    obtain ⟨d1, p1, hd1, h1⟩ := signed_walk_step phase stage (remaining+moves.length)
      (Cantor.pair move (Schedule.packCoordinates moves tail)) env formula reserve htag
    simp only [Cantor.unpair_pair] at h1
    obtain ⟨d2, p2, hd2, h2⟩ := ih (!phase) (Cantor.pair (move-1) env)
      (M236Game.child formula move) (reserve ++ List.replicate p1 0) htail
    have h := h1.trans graphSystem h2
    refine ⟨d1+d2, p1+p2, by simp only [List.length_cons]; omega, ?_⟩
    have hr : (reserve ++ List.replicate p1 0) ++ List.replicate p2 0 =
        reserve ++ List.replicate (p1+p2) 0 := by
      simp only [List.append_assoc, ← List.replicate_add]
    rw [hr] at h
    simpa [Schedule.packCoordinates, signedMovesPhase, signedMovesEnvironment, signedMovesFormula,
      PASoundness.UnaryCodec.encodeFields, Nat.add_assoc] using h

/-- The abstract encoded evaluator has the same child/environment/phase
transformation on any non-atomic finite prefix and arbitrary suffix. -/
theorem encoded_path_nonatomic_moves (moves suffix : List Nat) (phase : Bool) (env formula : Nat)
    (hnonatomic : NonatomicMoves formula moves) :
    M236Game.encodedPath formula env phase (moves ++ suffix) =
      M236Game.encodedPath (signedMovesFormula formula moves) (signedMovesEnvironment env moves)
        (signedMovesPhase phase moves) suffix := by
  induction moves generalizing phase env formula with
  | nil => rfl
  | cons move moves ih =>
    rw [List.cons_append, encoded_nonatomic_clause formula env move phase (moves ++ suffix) hnonatomic.1]
    simpa [signedMovesFormula, signedMovesEnvironment, signedMovesPhase] using
      ih (!phase) (Cantor.pair (move-1) env) (M236Game.child formula move) hnonatomic.2

/-- Physical lift for the finite list. Strict physical progress is asserted
only when at least one move is consumed. -/
theorem selected_signed_walk_moves (i : Nat) (moves : List Nat) (phase : Bool)
    (stage remaining tail env formula : Nat) (reserve : List Nat)
    (hnonatomic : NonatomicMoves formula moves)
    (h : graphSystem.run i =
      signedWalkCfg phase stage (remaining+moves.length) (Schedule.packCoordinates moves tail) env formula reserve) :
    ∃ duration padding finish, moves.length ≤ duration ∧ Good finish ∧
      finish.graphState = signedWalkCfg (signedMovesPhase phase moves) stage remaining tail
        (signedMovesEnvironment env moves) (signedMovesFormula formula moves) (reserve ++ List.replicate padding 0) ∧
      graphSystem.run (i+duration) = signedWalkCfg (signedMovesPhase phase moves) stage remaining tail
        (signedMovesEnvironment env moves) (signedMovesFormula formula moves) (reserve ++ List.replicate padding 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run (graphRefinement.boundary (i+duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++
          PASoundness.UnaryCodec.encodeFields moves ∧
      (moves ≠ [] → graphRefinement.boundary i < graphRefinement.boundary (i+duration)) := by
  obtain ⟨duration, padding, ht, block⟩ := signed_walk_moves moves phase stage remaining tail env formula reserve hnonatomic
  have hr : graphSystem.run (i+duration) = signedWalkCfg (signedMovesPhase phase moves) stage remaining tail
      (signedMovesEnvironment env moves) (signedMovesFormula formula moves) (reserve ++ List.replicate padding 0) := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i+duration) = graphSystem.prefixWord i ++ PASoundness.UnaryCodec.encodeFields moves := by
    rw [WordEventSystem.prefix_add, h, block.output]
  obtain ⟨finish, hg, hstate, hconfig⟩ := graphRefinement.related (i+duration)
  refine ⟨duration, padding, finish, ht, hg, hstate.trans hr, hr, hconfig, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · intro hne
    apply graphRefinement.boundary_strict
    have hlen : 0 < moves.length := List.length_pos_iff.mpr hne
    omega

/-- A zero counter at either prepared phase times out before inspecting the
formula, emits false, and clears the bank for the next scheduler stage. -/
theorem signed_walk_timeout_core (start : Nat) (mr : SignedMoveRows start)
    (dr : CounterDispatchRows (start+3)) (stage rest env formula : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgExact start (signedWalkBank stage 0 rest env formula) reserve)
      ((3*formula+1)+3+(2*(rest+env+formula)+8))
      (cfg 0 BlankFirst.zeros (stage+1) 0 0
        (reserve ++ List.replicate (formula+(rest+env+formula)) 0)) [false] := by
  let W := signedWalkBank stage 0 rest env formula
  have he := signed_walk_entry_view start stage 0 rest env formula reserve
  have hcount : W 3 = 0 := by simp [W, signedWalkBank]
  have h1 := signed_move_all formula start mr W 0 reserve
  simp only [Nat.zero_add] at h1
  rw [← he] at h1
  rw [timeout_count_zero_exit (start+3) W formula 0 _ hcount] at h1
  have h2 := counter_dispatch_zero 0 (start+3) dr (timeoutBank W formula 0)
    (reserve ++ List.replicate formula 0)
  simp only [List.replicate_zero, List.append_nil, Nat.mul_zero, Nat.zero_add] at h2
  have hstate : cfgCountTop 724 (timeoutBank W formula 0) 0 0 (reserve ++ List.replicate formula 0) =
      cfgTimeout 724 W formula 0 (reserve ++ List.replicate formula 0) := by
    unfold cfgCountTop cfgTimeout
    congr 1
    funext j
    fin_cases j <;> simp [bankCountTop, timeoutBank, W, signedWalkBank]
  rw [hstate] at h2
  have h0 : W 0 = 0 := by simp [W, signedWalkBank]
  have h6 : W 6 = 0 := by simp [W, signedWalkBank]
  have h8 : W 8 = 0 := by simp [W, signedWalkBank]
  have h3 := timeout_final_cleanup W formula (reserve ++ List.replicate formula 0) h0 hcount h6 h8
  have h := (h1.trans graphSystem h2).trans graphSystem h3
  have hr : (reserve ++ List.replicate formula 0) ++ List.replicate (rest+env+formula) 0 =
      reserve ++ List.replicate (formula+(rest+env+formula)) 0 := by
    simp only [List.append_assoc, ← List.replicate_add]
  have hrest : W 2 = rest := by simp [W, signedWalkBank]
  have henv : W 5 = env := by simp [W, signedWalkBank]
  have hstage : W 1 = stage := by simp [W, signedWalkBank]
  rw [hrest, henv, hstage, hr] at h
  simpa using h

theorem signed_walk_timeout (phase : Bool) (stage rest env formula : Nat) (reserve : List Nat) :
    graphSystem.Block (signedWalkCfg phase stage 0 rest env formula reserve)
      ((3*formula+1)+3+(2*(rest+env+formula)+8))
      (cfg 0 BlankFirst.zeros (stage+1) 0 0
        (reserve ++ List.replicate (formula+(rest+env+formula)) 0)) [false] := by
  cases phase with
  | false =>
    simpa [signedWalkCfg, signedWalkIndex] using
      signed_walk_timeout_core 366 signed_move_rows_366 timeout_rows_369 stage rest env formula reserve
  | true =>
    simpa [signedWalkCfg, signedWalkIndex] using
      signed_walk_timeout_core 546 signed_move_rows_546 signed_dispatch_rows_549 stage rest env formula reserve

/-- Exhausting exactly the finite non-atomic move budget emits the entire
coordinate suffix, then the false result, and returns to a clean next stage. -/
theorem signed_walk_moves_timeout (moves : List Nat) (phase : Bool) (stage tail env formula : Nat)
    (reserve : List Nat) (hnonatomic : NonatomicMoves formula moves) :
    ∃ duration padding, moves.length+1 ≤ duration ∧
      graphSystem.Block
        (signedWalkCfg phase stage moves.length (Schedule.packCoordinates moves tail) env formula reserve) duration
        (cfg 0 BlankFirst.zeros (stage+1) 0 0 (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.encodeFields moves ++ [false]) := by
  obtain ⟨d1, p1, hd1, h1⟩ := signed_walk_moves moves phase stage 0 tail env formula reserve hnonatomic
  simp only [Nat.zero_add] at h1
  have h2 := signed_walk_timeout (signedMovesPhase phase moves) stage tail
    (signedMovesEnvironment env moves) (signedMovesFormula formula moves) (reserve ++ List.replicate p1 0)
  have h := h1.trans graphSystem h2
  refine ⟨d1+((3*(signedMovesFormula formula moves)+1)+3+
      (2*(tail+signedMovesEnvironment env moves+signedMovesFormula formula moves)+8)),
    p1+(signedMovesFormula formula moves+(tail+signedMovesEnvironment env moves+signedMovesFormula formula moves)),
    by omega, ?_⟩
  have hr : (reserve ++ List.replicate p1 0) ++
      List.replicate (signedMovesFormula formula moves+(tail+signedMovesEnvironment env moves+signedMovesFormula formula moves)) 0 =
      reserve ++ List.replicate (p1+(signedMovesFormula formula moves+(tail+signedMovesEnvironment env moves+signedMovesFormula formula moves))) 0 := by
    simp only [List.append_assoc, ← List.replicate_add]
  rw [hr] at h
  exact h

/-- On exactly the supplied non-atomic moves, the abstract encoded evaluator
also times out with its optimistic `true` value. The final formula can be
atomic because it is not inspected once the move list is empty. -/
theorem encoded_nonatomic_timeout (moves : List Nat) (phase : Bool) (env formula : Nat)
    (hnonatomic : NonatomicMoves formula moves) :
    M236Game.encodedPath formula env phase moves = true := by
  have h := encoded_path_nonatomic_moves moves [] phase env formula hnonatomic
  simpa [M236Game.encodedPath] using h

/-- Physical lift of the exact-budget timeout, conditional on reaching the
prepared graph boundary. Positive physical progress holds even for no moves. -/
theorem selected_signed_walk_moves_timeout (i : Nat) (moves : List Nat) (phase : Bool)
    (stage tail env formula : Nat) (reserve : List Nat) (hnonatomic : NonatomicMoves formula moves)
    (h : graphSystem.run i =
      signedWalkCfg phase stage moves.length (Schedule.packCoordinates moves tail) env formula reserve) :
    ∃ duration padding finish, moves.length+1 ≤ duration ∧ Good finish ∧
      finish.graphState = cfg 0 BlankFirst.zeros (stage+1) 0 0 (reserve ++ List.replicate padding 0) ∧
      graphSystem.run (i+duration) = cfg 0 BlankFirst.zeros (stage+1) 0 0 (reserve ++ List.replicate padding 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run (graphRefinement.boundary (i+duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++
          (PASoundness.UnaryCodec.encodeFields moves ++ [false]) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i+duration) := by
  obtain ⟨duration, padding, ht, block⟩ := signed_walk_moves_timeout moves phase stage tail env formula reserve hnonatomic
  have hr : graphSystem.run (i+duration) = cfg 0 BlankFirst.zeros (stage+1) 0 0 (reserve ++ List.replicate padding 0) := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i+duration) = graphSystem.prefixWord i ++
      (PASoundness.UnaryCodec.encodeFields moves ++ [false]) := by
    rw [WordEventSystem.prefix_add, h, block.output]
  obtain ⟨finish, hg, hstate, hconfig⟩ := graphRefinement.related (i+duration)
  refine ⟨duration, padding, finish, ht, hg, hstate.trans hr, hr, hconfig, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

end PASoundness.M236.OccurrenceGraph
