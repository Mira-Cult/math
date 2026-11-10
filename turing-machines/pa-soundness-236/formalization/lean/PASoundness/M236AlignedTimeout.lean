import PASoundness.M236SignedWalk

/-! Prepared aligned non-atomic timeout paths and their source-value boundary. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

theorem signed_move_rows_189 : SignedMoveRows 189 := by constructor <;> decide

/-- The initial negative-phase row 189 consumes exactly the supplied moves,
then times out and returns to the next scheduler stage. -/
theorem signed_189_moves_timeout (moves : List Nat) (stage tail env formula : Nat)
    (reserve : List Nat) (hnonatomic : NonatomicMoves formula moves) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block
        (cfgExact 189 (signedWalkBank stage moves.length (Schedule.packCoordinates moves tail) env formula) reserve) duration
        (cfg 0 BlankFirst.zeros (stage+1) 0 0 (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.encodeFields moves ++ [false]) := by
  cases moves with
  | nil =>
    refine ⟨(3*formula+1)+3+(2*(tail+env+formula)+8), formula+(tail+env+formula), by omega, ?_⟩
    simpa [Schedule.packCoordinates, PASoundness.UnaryCodec.encodeFields] using
      signed_walk_timeout_core 189 signed_move_rows_189 signed_dispatch_rows_192 stage tail env formula reserve
  | cons move moves =>
    have htag : (Cantor.unpair formula).1 ≠ 0 := hnonatomic.1
    have htail : NonatomicMoves (M236Game.child formula move) moves := hnonatomic.2
    obtain ⟨d1, p1, hd1, h1⟩ := signed_walk_core 189 366 signed_move_rows_189
      signed_dispatch_rows_192 signed_unpair_rows_197 signed_emit_rows_208 formula_scan_rows_216 formula_branch_row_216
      child_rows_225 pair_env_rows_237 child_next_225 stage moves.length
      (Cantor.pair move (Schedule.packCoordinates moves tail)) env formula reserve htag
    simp only [Cantor.unpair_pair] at h1
    obtain ⟨d2, p2, hd2, h2⟩ := signed_walk_moves_timeout moves false stage tail
      (Cantor.pair (move-1) env) (M236Game.child formula move) (reserve ++ List.replicate p1 0) htail
    have h := h1.trans graphSystem h2
    refine ⟨d1+d2, p1+p2, by omega, ?_⟩
    have hr : (reserve ++ List.replicate p1 0) ++ List.replicate p2 0 =
        reserve ++ List.replicate (p1+p2) 0 := by
      simp only [List.append_assoc, ← List.replicate_add]
    rw [hr] at h
    simpa [Schedule.packCoordinates, signedWalkCfg, signedWalkIndex,
      PASoundness.UnaryCodec.encodeFields, List.append_assoc] using h

/-- A one-bit initial polarity enters row 366 without consuming a move. -/
theorem aligned_one_enter (stage count rest env formula : Nat) (reserve : List Nat) :
    graphSystem.Block
      (cfgTimeout 161 (signedWalkBank stage count rest env formula) 1 formula reserve) 2
      (signedWalkCfg false stage count rest env formula (reserve ++ [0])) [] := by
  let W := signedWalkBank stage count rest env formula
  have h1 := WordEventSystem.Block.single graphSystem (timeout_bit_one W formula reserve)
  have h2 := WordEventSystem.Block.single graphSystem (timeout_jump162 W 0 formula (reserve ++ [0]))
  have he := signed_walk_entry_view 366 stage count rest env formula (reserve ++ [0])
  rw [← he] at h2
  simpa [signedWalkCfg, signedWalkIndex, W] using h1.trans graphSystem h2

/-- If the selected bit is one, all remaining coordinates are evaluated; a
non-atomic exact-budget suffix ends with a false bit and clean return. -/
theorem aligned_one_timeout (moves : List Nat) (stage tail env formula : Nat)
    (reserve : List Nat) (hnonatomic : NonatomicMoves formula moves) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block
        (cfgTimeout 161 (signedWalkBank stage moves.length (Schedule.packCoordinates moves tail) env formula) 1 formula reserve) duration
        (cfg 0 BlankFirst.zeros (stage+1) 0 0 (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.encodeFields moves ++ [false]) := by
  have h1 := aligned_one_enter stage moves.length (Schedule.packCoordinates moves tail) env formula reserve
  obtain ⟨d, p, hd, h2⟩ := signed_walk_moves_timeout moves false stage tail env formula (reserve ++ [0]) hnonatomic
  have h := h1.trans graphSystem h2
  refine ⟨2+d, 1+p, by omega, ?_⟩
  have hr : (reserve ++ [0]) ++ List.replicate p 0 = reserve ++ List.replicate (1+p) 0 := by
    change (reserve ++ List.replicate 1 0) ++ List.replicate p 0 = _
    simp only [List.append_assoc, ← List.replicate_add]
  rw [hr] at h
  simpa using h

/-- A zero-bit alignment with no remaining coordinates times out immediately. -/
theorem aligned_zero_empty_timeout (stage tail env formula : Nat) (reserve : List Nat) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block (cfgTimeout 161 (signedWalkBank stage 0 tail env formula) 0 formula reserve) duration
        (cfg 0 BlankFirst.zeros (stage+1) 0 0 (reserve ++ List.replicate padding 0)) [false] := by
  let W := signedWalkBank stage 0 tail env formula
  obtain ⟨duration, padding, ht, h⟩ := timeout_false_frame false W formula reserve
    (by simp [W, signedWalkBank]) (by simp [W, signedWalkBank])
    (by simp [W, signedWalkBank]) (by simp [W, signedWalkBank])
  exact ⟨duration, padding, ht, by simpa [W, signedWalkBank] using h⟩

/-- A zero-bit alignment consumes its first coordinate without evaluating it;
the non-atomic requirement applies only to the remaining moves. -/
theorem aligned_zero_cons_timeout (alignment : Nat) (moves : List Nat) (stage tail env formula : Nat)
    (reserve : List Nat) (hnonatomic : NonatomicMoves formula moves) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block
        (cfgTimeout 161 (signedWalkBank stage (moves.length+1)
          (Schedule.packCoordinates (alignment :: moves) tail) env formula) 0 formula reserve) duration
        (cfg 0 BlankFirst.zeros (stage+1) 0 0 (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.encodeFields (alignment :: moves) ++ [false]) := by
  let W := signedWalkBank stage (moves.length+1)
    (Cantor.pair alignment (Schedule.packCoordinates moves tail)) env formula
  have h0 : W 0 = 0 := by simp [W, signedWalkBank]
  have hn : W 3 = moves.length+1 := by simp [W, signedWalkBank]
  have ha : W 6 = 0 := by simp [W, signedWalkBank]
  have hc : W 8 = 0 := by simp [W, signedWalkBank]
  obtain ⟨d1, p1, hd1, h1⟩ := positive_zero_to_189 W moves.length formula reserve h0 hn ha hc
  have hview : positiveZeroExit W moves.length formula reserve p1 =
      cfgExact 189 (signedWalkBank stage moves.length (Schedule.packCoordinates moves tail) env formula)
        (reserve ++ List.replicate (1+p1+alignment+alignment+alignment) 0) := by
    have hr : (((((reserve ++ [0]) ++ List.replicate p1 0) ++ List.replicate alignment 0) ++
        List.replicate alignment 0) ++ List.replicate alignment 0) =
        reserve ++ List.replicate (1+p1+alignment+alignment+alignment) 0 := by
      change (((((reserve ++ List.replicate 1 0) ++ List.replicate p1 0) ++ List.replicate alignment 0) ++
        List.replicate alignment 0) ++ List.replicate alignment 0) = _
      simp only [List.append_assoc, ← List.replicate_add]
    unfold positiveZeroExit cfgAS cfgExact
    simp only [show W 2 = Cantor.pair alignment (Schedule.packCoordinates moves tail) by simp [W, signedWalkBank],
      Cantor.unpair_pair]
    rw [hr]
    congr 1
    funext j
    fin_cases j <;> simp [bankAS, bankAC, bankRest, bankCountTop, timeoutBank, W, signedWalkBank]
  rw [hview] at h1
  obtain ⟨d2, p2, hd2, h2⟩ := signed_189_moves_timeout moves stage tail env formula
    (reserve ++ List.replicate (1+p1+alignment+alignment+alignment) 0) hnonatomic
  have h := h1.trans graphSystem h2
  refine ⟨(1+(2+(d1+(7*alignment+3))))+(2*alignment+1)+d2,
    (1+p1+alignment+alignment+alignment)+p2, by omega, ?_⟩
  have hr : (reserve ++ List.replicate (1+p1+alignment+alignment+alignment) 0) ++ List.replicate p2 0 =
      reserve ++ List.replicate ((1+p1+alignment+alignment+alignment)+p2) 0 := by
    simp only [List.append_assoc, ← List.replicate_add]
  rw [hr] at h
  simpa [W, signedWalkBank, Schedule.packCoordinates, Cantor.unpair_pair,
    PASoundness.UnaryCodec.encodeFields, List.append_assoc] using h

/-- Both initial polarities, with the alignment coordinate excluded from the
non-atomic condition precisely in the zero-bit case. -/
theorem aligned_timeout (bit : Bool) (moves : List Nat) (stage tail env formula : Nat)
    (reserve : List Nat) (hnonatomic : NonatomicMoves formula (if bit then moves else moves.drop 1)) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block
        (cfgTimeout 161 (signedWalkBank stage moves.length (Schedule.packCoordinates moves tail) env formula)
          (if bit then 1 else 0) formula reserve) duration
        (cfg 0 BlankFirst.zeros (stage+1) 0 0 (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.encodeFields moves ++ [false]) := by
  cases bit with
  | true =>
    exact aligned_one_timeout moves stage tail env formula reserve (by simpa using hnonatomic)
  | false =>
    cases moves with
    | nil =>
      simpa [Schedule.packCoordinates, PASoundness.UnaryCodec.encodeFields] using
        aligned_zero_empty_timeout stage tail env formula reserve
    | cons alignment moves =>
      simpa using aligned_zero_cons_timeout alignment moves stage tail env formula reserve (by simpa using hnonatomic)

/-- Independent abstract specification: this same non-atomic timeout path
has false selected value, whether or not the bounded graph premise holds. -/
theorem selected_nonatomic_timeout (f c y : Nat) (rest : List Nat)
    (hn : NonatomicMoves f (if c.testBit y then rest else rest.drop 1)) :
    M236Game.selectedValue ⟨rest.length+2, f, c :: y :: rest⟩ = false := by
  rw [← M236Game.selected_encoded_value]
  cases hb : c.testBit y with
  | false =>
    cases rest with
    | nil => simp [M236Game.selectedEncodedValue, M236Game.encodedAligned, hb]
    | cons alignment moves =>
      have ht := encoded_nonatomic_timeout moves true (Cantor.pair y 0) f (by simpa [hb] using hn)
      simp [M236Game.selectedEncodedValue, M236Game.encodedAligned, hb, ht]
  | true =>
    have ht := encoded_nonatomic_timeout rest false (Cantor.pair y 0) f (by simpa [hb] using hn)
    simp [M236Game.selectedEncodedValue, M236Game.encodedAligned, hb, ht]

/-- From a prepared bounded second-coordinate emitter with clean initial env,
the exact-budget aligned non-atomic suffix emits false and returns clean. -/
theorem bounded_aligned_timeout (n : Nat) (moves : List Nat) (tail : Nat)
    (base : RegisterMachine.Bank 9) (reserve : List Nat)
    (hc : base 8 = 0) (hcount : base 3 = moves.length) (hbudget : n ≤ moves.length)
    (henv : base 5 = 0) (hrest : base 2 = Schedule.packCoordinates moves tail)
    (hnonatomic : NonatomicMoves (base 4) (if (base 7).testBit n then moves else moves.drop 1)) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block (cfgAS 103 base n 0 reserve) duration
        (cfg 0 BlankFirst.zeros (base 1+1) 0 0 (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.encodeFields moves ++ [false]) := by
  have hcount' : base 3 = (moves.length-n)+n := by omega
  obtain ⟨d1, p1, hd1, h1⟩ := budget_success_then_initialize n (moves.length-n) base reserve hc hcount'
  let r := reserve ++ List.replicate (3*n+p1) 0
  have hview : cfgBudget 161 (boundedBitBank base n) (base 3) (Cantor.pair (base 5+n) 0) 0 0 r =
      cfgTimeout 161 (signedWalkBank (base 1) moves.length (Schedule.packCoordinates moves tail)
        (Cantor.pair n 0) (base 4)) (if (base 7).testBit n then 1 else 0) (base 4) r := by
    unfold cfgBudget cfgTimeout
    congr 1
    funext j
    fin_cases j <;> simp [boundedBitBank, bankBudget, bankHalf, bankAS, timeoutBank, signedWalkBank,
      hcount, henv, hrest]
  rw [hview] at h1
  obtain ⟨d2, p2, hd2, h2⟩ := aligned_timeout ((base 7).testBit n) moves (base 1) tail
    (Cantor.pair n 0) (base 4) r hnonatomic
  have h := h1.trans graphSystem h2
  refine ⟨((10*n+2)+d1)+d2, (3*n+p1)+p2, by omega, ?_⟩
  have hr : r ++ List.replicate p2 0 = reserve ++ List.replicate ((3*n+p1)+p2) 0 := by
    dsimp [r]
    simp only [List.append_assoc, ← List.replicate_add]
  rw [hr] at h
  exact h

/-- Conditional physical lift of the complete prepared bounded suffix. -/
theorem selected_bounded_aligned_timeout (i n : Nat) (moves : List Nat) (tail : Nat)
    (base : RegisterMachine.Bank 9) (reserve : List Nat)
    (hc : base 8 = 0) (hcount : base 3 = moves.length) (hbudget : n ≤ moves.length)
    (henv : base 5 = 0) (hrest : base 2 = Schedule.packCoordinates moves tail)
    (hnonatomic : NonatomicMoves (base 4) (if (base 7).testBit n then moves else moves.drop 1))
    (h : graphSystem.run i = cfgAS 103 base n 0 reserve) :
    ∃ duration padding finish, 0 < duration ∧ Good finish ∧
      finish.graphState = cfg 0 BlankFirst.zeros (base 1+1) 0 0 (reserve ++ List.replicate padding 0) ∧
      graphSystem.run (i+duration) = cfg 0 BlankFirst.zeros (base 1+1) 0 0 (reserve ++ List.replicate padding 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run (graphRefinement.boundary (i+duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++
          (PASoundness.UnaryCodec.encodeFields moves ++ [false]) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i+duration) := by
  obtain ⟨duration, padding, ht, block⟩ := bounded_aligned_timeout n moves tail base reserve hc hcount hbudget henv hrest hnonatomic
  have hr : graphSystem.run (i+duration) = cfg 0 BlankFirst.zeros (base 1+1) 0 0 (reserve ++ List.replicate padding 0) := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i+duration) = graphSystem.prefixWord i ++
      (PASoundness.UnaryCodec.encodeFields moves ++ [false]) := by
    rw [WordEventSystem.prefix_add, h, block.output]
  obtain ⟨finish, hg, hstate, hconfig⟩ := graphRefinement.related (i+duration)
  refine ⟨duration, padding, finish, ht, hg, hstate.trans hr, hr, hconfig, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

/-- The decoded finite prefix and its residual tail reconstruct any packed
coordinate code, with no bound or canonical-tail assumption. -/
theorem pack_decode_residual (n code : Nat) :
    Schedule.packCoordinates (Schedule.decodeCoordinates n code) (residualTail n code) = code := by
  induction n generalizing code with
  | zero => rfl
  | succ n ih =>
    simp [Schedule.decodeCoordinates, residualTail, Schedule.packCoordinates, ih, Cantor.pair_unpair]

def stageRemainingMoves (stage count : Nat) : List Nat :=
  Schedule.decodeCoordinates count (Cantor.unpair (stageRemaining stage)).2

def stageFormula (stage : Nat) : Nat := (Cantor.unpair (Cantor.unpair stage).2).1

def stageChallenge (stage : Nat) : Nat :=
  (Cantor.unpair (Cantor.unpair (Cantor.unpair stage).2).2).1

/-- The selected source value is false on a scheduled non-atomic timeout. -/
theorem scheduled_nonatomic_timeout (stage count : Nat)
    (hpositive : (Cantor.unpair stage).1 = count+1)
    (hn : NonatomicMoves (stageFormula stage)
      (if (stageChallenge stage).testBit (stageSecondCoordinate stage) then stageRemainingMoves stage count
       else (stageRemainingMoves stage count).drop 1)) :
    M236Game.selectedValue (Schedule.scheduledAddress stage) = false := by
  have h := selected_nonatomic_timeout (stageFormula stage) (stageChallenge stage) (stageSecondCoordinate stage)
    (stageRemainingMoves stage count) hn
  simpa [stageFormula, stageChallenge, stageRemainingMoves, Schedule.scheduledAddress,
    Schedule.decodeCoordinates, stageSecondCoordinate, stageRemaining, hpositive, Nat.add_assoc] using h

/-- Exact clean-scheduler bank projections after the first four fields. -/
theorem stage_four_clean_projections (stage : Nat) (reserve : List Nat)
    (firstPadding padding nextPadding count : Nat) :
    let b := stageFourBudgetBank BlankFirst.zeros stage reserve firstPadding padding nextPadding count
    b 1 = stage ∧ b 2 = (Cantor.unpair (stageRemaining stage)).2 ∧ b 3 = count ∧
    b 4 = stageFormula stage ∧ b 5 = 0 ∧ b 7 = stageChallenge stage ∧ b 8 = 0 := by
  simp [stageFourBudgetBank, stageFourthBase, stageThreeExit, thirdFieldExit, cfgFieldTransfer,
    bankFieldTransfer, bankAS, thirdFieldBank, bankAC, bankRest, bankOnlyCount,
    secondTopState, secondDecodedBank, secondFieldBase, bankCountA, bankCountTop,
    stageRankBank, rankBase, bankWith, BlankFirst.zeros, thirdFieldValue, stageFormula,
    stageChallenge, stageRemaining]

/-- A clean scheduler stage in the bounded, non-atomic-timeout subcase emits
exactly its selected source frame and returns to the next clean stage. The
condition is polarity-sensitive: a zero selected bit skips one alignment move. -/
theorem scheduler_bounded_nonatomic_frame (stage count : Nat) (reserve : List Nat)
    (hpositive : (Cantor.unpair stage).1 = count+1) (hbudget : stageSecondCoordinate stage ≤ count)
    (hn : NonatomicMoves (stageFormula stage)
      (if (stageChallenge stage).testBit (stageSecondCoordinate stage) then stageRemainingMoves stage count
       else (stageRemainingMoves stage count).drop 1)) :
    ∃ steps nextReserve, 0 < steps ∧
      graphSystem.Block (cfg 0 BlankFirst.zeros stage 0 0 reserve) steps
        (cfg 0 BlankFirst.zeros (stage+1) 0 0 nextReserve)
        (PASoundness.UnaryCodec.encodeFrame (Schedule.scheduledAddress stage)
          (M236Game.selectedValue (Schedule.scheduledAddress stage))) := by
  obtain ⟨d1, p1, d2, p2, d3, p3, d4, p4, ht1, ht2, ht3, ht4, hfour⟩ :=
    scheduler_first_four_fields stage count BlankFirst.zeros reserve rfl rfl rfl hpositive
  let b := stageFourBudgetBank BlankFirst.zeros stage reserve p1 p2 p3 count
  let r := stageFourBudgetReserve BlankFirst.zeros stage reserve p1 p2 p3 p4
  let q := stageSecondCoordinate stage
  let moves := stageRemainingMoves stage count
  let tail := residualTail count (Cantor.unpair (stageRemaining stage)).2
  change graphSystem.Block (cfg 0 BlankFirst.zeros stage 0 0 reserve) _ (cfgAS 103 b q 0 r) _ at hfour
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb7, hb8⟩ := stage_four_clean_projections stage reserve p1 p2 p3 count
  change b 1 = stage at hb1
  change b 2 = (Cantor.unpair (stageRemaining stage)).2 at hb2
  change b 3 = count at hb3
  change b 4 = stageFormula stage at hb4
  change b 5 = 0 at hb5
  change b 7 = stageChallenge stage at hb7
  change b 8 = 0 at hb8
  have hlen : moves.length = count := by simp [moves, stageRemainingMoves]
  have hrest : b 2 = Schedule.packCoordinates moves tail := by
    change b 2 = Schedule.packCoordinates
      (Schedule.decodeCoordinates count (Cantor.unpair (stageRemaining stage)).2)
      (residualTail count (Cantor.unpair (stageRemaining stage)).2)
    rw [pack_decode_residual]
    exact hb2
  have hcount : b 3 = moves.length := by rw [hlen]; exact hb3
  have hbudget' : q ≤ moves.length := by simpa [q, hlen] using hbudget
  have hnonatomic : NonatomicMoves (b 4) (if (b 7).testBit q then moves else moves.drop 1) := by
    simpa [hb4, hb7, q, moves] using hn
  obtain ⟨d5, p5, ht5, hsuffix⟩ := bounded_aligned_timeout q moves tail b r hb8 hcount hbudget' hb5 hrest hnonatomic
  rw [hb1] at hsuffix
  have h := hfour.trans graphSystem hsuffix
  have hw : stageFourWord stage ++ (PASoundness.UnaryCodec.encodeFields moves ++ [false]) =
      PASoundness.UnaryCodec.encodeFrame (Schedule.scheduledAddress stage)
        (M236Game.selectedValue (Schedule.scheduledAddress stage)) := by
    rw [← List.append_assoc]
    have hword := stage_overflow_address_word stage count hpositive
    change stageFourWord stage ++ PASoundness.UnaryCodec.encodeFields moves = _ at hword
    rw [hword, encode_fields_false_frame, scheduled_nonatomic_timeout stage count hpositive hn]
  rw [hw] at h
  exact ⟨_, _, by omega, h⟩

/-- Physical lift conditional on the clean scheduler entry occurring on the
actual selected blank-start execution. -/
theorem selected_scheduler_bounded_nonatomic_frame (i stage count : Nat) (reserve : List Nat)
    (hpositive : (Cantor.unpair stage).1 = count+1) (hbudget : stageSecondCoordinate stage ≤ count)
    (hn : NonatomicMoves (stageFormula stage)
      (if (stageChallenge stage).testBit (stageSecondCoordinate stage) then stageRemainingMoves stage count
       else (stageRemainingMoves stage count).drop 1))
    (h : graphSystem.run i = cfg 0 BlankFirst.zeros stage 0 0 reserve) :
    ∃ steps nextReserve finish, 0 < steps ∧ Good finish ∧
      finish.graphState = cfg 0 BlankFirst.zeros (stage+1) 0 0 nextReserve ∧
      graphSystem.run (i+steps) = cfg 0 BlankFirst.zeros (stage+1) 0 0 nextReserve ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run (graphRefinement.boundary (i+steps)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+steps)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++
          PASoundness.UnaryCodec.encodeFrame (Schedule.scheduledAddress stage)
            (M236Game.selectedValue (Schedule.scheduledAddress stage)) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i+steps) := by
  obtain ⟨steps, nextReserve, ht, block⟩ := scheduler_bounded_nonatomic_frame stage count reserve hpositive hbudget hn
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
