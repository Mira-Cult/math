import PASoundness.M236SignedAtomWalk
import PASoundness.M236FrameSegmentation

/-! Finite first-atom decomposition and bounded scheduler-frame composition. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

/-- A first atom occurs at a paid move after a finite non-atomic pre. -/
def FirstAtom (formula : Nat) (moves : List Nat) : Prop :=
  ∃ pre paid suffix, moves = pre ++ paid :: suffix ∧
    NonatomicMoves formula pre ∧ (Cantor.unpair (signedMovesFormula formula pre)).1 = 0

/-- Every finite path either spends all of its budget at non-atoms or has a
first atom with a paid move. Empty paths are timeouts. -/
theorem finite_first_atom_split (formula : Nat) (moves : List Nat) :
    NonatomicMoves formula moves ∨ FirstAtom formula moves := by
  induction moves generalizing formula with
  | nil => exact Or.inl trivial
  | cons move moves ih =>
    by_cases htag : (Cantor.unpair formula).1 = 0
    · right
      exact ⟨[], move, moves, rfl, trivial, htag⟩
    · rcases ih (M236Game.child formula move) with hn | ⟨pre, paid, suffix, hlist, hp, ha⟩
      · exact Or.inl ⟨htag, hn⟩
      · right
        refine ⟨move :: pre, paid, suffix, ?_, ?_, ?_⟩
        · simp [hlist]
        · exact ⟨htag, hp⟩
        · simpa [signedMovesFormula] using ha

theorem pack_pre_append (pre suffix : List Nat) (tail : Nat) :
    Schedule.packCoordinates (pre ++ suffix) tail =
      Schedule.packCoordinates pre (Schedule.packCoordinates suffix tail) := by
  induction pre with
  | nil => rfl
  | cons move pre ih => simp [Schedule.packCoordinates, ih]

/-- A one-bit prepared entry with a first atomic paid move emits its entire
remaining coordinate word and selected payoff. -/
theorem aligned_one_atom_list (pre suffix : List Nat) (stage paid tail formula challenge y : Nat)
    (reserve : List Nat) (hn : NonatomicMoves formula pre)
    (ha : (Cantor.unpair (signedMovesFormula formula pre)).1 = 0)
    (hy : y ≤ (pre ++ paid :: suffix).length) (hbit : challenge.testBit y = true) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block
        (cfgTimeout 161 (signedWalkBank stage (pre ++ paid :: suffix).length
          (Schedule.packCoordinates (pre ++ paid :: suffix) tail) (Cantor.pair y 0) formula) 1 formula reserve) duration
        (cfg 0 BlankFirst.zeros (stage+1) 0 0 (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.encodeFields (pre ++ paid :: suffix) ++
          PASoundness.UnaryCodec.unary (PASoundness.UnaryCodec.bitNat
            (M236Game.selectedValue ⟨(pre ++ paid :: suffix).length+2,
              formula, challenge :: y :: (pre ++ paid :: suffix)⟩))) := by
  have h := aligned_one_first_atom_selected pre stage suffix.length paid (Schedule.packCoordinates suffix tail)
    formula challenge y reserve hn ha (by simpa using hy) hbit
  simpa [Schedule.decode_pack, pack_pre_append, Schedule.packCoordinates, PASoundness.M236FrameSegmentation.encodeFields_append,
    PASoundness.UnaryCodec.encodeFields, List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- A zero-bit prepared entry emits and skips alignment before the evaluated
non-atomic pre and first paid atom. -/
theorem aligned_zero_atom_list (alignment : Nat) (pre suffix : List Nat)
    (stage paid tail formula challenge y : Nat) (reserve : List Nat)
    (hn : NonatomicMoves formula pre) (ha : (Cantor.unpair (signedMovesFormula formula pre)).1 = 0)
    (hy : y ≤ (alignment :: (pre ++ paid :: suffix)).length) (hbit : challenge.testBit y = false) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block
        (cfgTimeout 161 (signedWalkBank stage (alignment :: (pre ++ paid :: suffix)).length
          (Schedule.packCoordinates (alignment :: (pre ++ paid :: suffix)) tail) (Cantor.pair y 0) formula) 0 formula reserve) duration
        (cfg 0 BlankFirst.zeros (stage+1) 0 0 (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.encodeFields (alignment :: (pre ++ paid :: suffix)) ++
          PASoundness.UnaryCodec.unary (PASoundness.UnaryCodec.bitNat
            (M236Game.selectedValue ⟨(alignment :: (pre ++ paid :: suffix)).length+2,
              formula, challenge :: y :: alignment :: (pre ++ paid :: suffix)⟩))) := by
  have h := aligned_zero_first_atom_selected alignment pre stage suffix.length paid (Schedule.packCoordinates suffix tail)
    formula challenge y reserve hn ha (by simpa using hy) hbit
  simpa [Schedule.decode_pack, pack_pre_append, Schedule.packCoordinates, PASoundness.M236FrameSegmentation.encodeFields_append,
    PASoundness.UnaryCodec.encodeFields, List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- Both initial alignments, with the first-atom condition applied only to
coordinates that the signed evaluator actually consumes. -/
theorem aligned_first_atom_list (moves : List Nat) (stage tail formula challenge y : Nat)
    (reserve : List Nat) (hy : y ≤ moves.length)
    (ha : FirstAtom formula (if challenge.testBit y then moves else moves.drop 1)) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block
        (cfgTimeout 161 (signedWalkBank stage moves.length (Schedule.packCoordinates moves tail)
          (Cantor.pair y 0) formula) (if challenge.testBit y then 1 else 0) formula reserve) duration
        (cfg 0 BlankFirst.zeros (stage+1) 0 0 (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.encodeFields moves ++
          PASoundness.UnaryCodec.unary (PASoundness.UnaryCodec.bitNat
            (M236Game.selectedValue ⟨moves.length+2, formula, challenge :: y :: moves⟩))) := by
  cases hb : challenge.testBit y with
  | true =>
    simp only [hb, if_true] at ha ⊢
    obtain ⟨pre, paid, suffix, heq, hn, hatom⟩ := ha
    subst moves
    exact aligned_one_atom_list pre suffix stage paid tail formula challenge y reserve hn hatom hy hb
  | false =>
    simp only [hb, Bool.false_eq_true, if_false] at ha ⊢
    cases moves with
    | nil => simp [FirstAtom] at ha
    | cons alignment moves =>
      simp only [List.drop_succ_cons, List.drop_zero] at ha
      obtain ⟨pre, paid, suffix, heq, hn, hatom⟩ := ha
      subst moves
      exact aligned_zero_atom_list alignment pre suffix stage paid tail formula challenge y reserve hn hatom hy hb

/-- Successful budget test and initialization, followed by the first-atom
case, emit the selected source's remaining fields and bit. -/
theorem bounded_aligned_first_atom (n : Nat) (moves : List Nat) (tail : Nat)
    (base : RegisterMachine.Bank 9) (reserve : List Nat)
    (hc : base 8 = 0) (hcount : base 3 = moves.length) (hbudget : n ≤ moves.length)
    (henv : base 5 = 0) (hrest : base 2 = Schedule.packCoordinates moves tail)
    (ha : FirstAtom (base 4) (if (base 7).testBit n then moves else moves.drop 1)) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block (cfgAS 103 base n 0 reserve) duration
        (cfg 0 BlankFirst.zeros (base 1+1) 0 0 (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.encodeFields moves ++
          PASoundness.UnaryCodec.unary (PASoundness.UnaryCodec.bitNat
            (M236Game.selectedValue ⟨moves.length+2, base 4, base 7 :: n :: moves⟩))) := by
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
  obtain ⟨d2, p2, hd2, h2⟩ := aligned_first_atom_list moves (base 1) tail (base 4) (base 7) n r hbudget ha
  have h := h1.trans graphSystem h2
  refine ⟨((10*n+2)+d1)+d2, (3*n+p1)+p2, by omega, ?_⟩
  have hr : r ++ List.replicate p2 0 = reserve ++ List.replicate ((3*n+p1)+p2) 0 := by
    dsimp [r]
    simp only [List.append_assoc, ← List.replicate_add]
  rw [hr] at h
  exact h

theorem encode_fields_boolean_frame (a : PASoundness.Observer.Address) (value : Bool) :
    PASoundness.UnaryCodec.encodeFields ([a.rank, a.certificate] ++ a.coordinates) ++
      PASoundness.UnaryCodec.unary (PASoundness.UnaryCodec.bitNat value) =
      PASoundness.UnaryCodec.encodeFrame a value := by
  simp [PASoundness.UnaryCodec.encodeFrame, PASoundness.UnaryCodec.frameFields,
    PASoundness.M236FrameSegmentation.encodeFields_append, PASoundness.UnaryCodec.encodeFields,
    List.append_assoc]

/-- A clean successful-budget scheduler entry with a first atomic move emits
its exact selected source frame and returns cleanly. -/
theorem scheduler_bounded_first_atom_frame (stage count : Nat) (reserve : List Nat)
    (hpositive : (Cantor.unpair stage).1 = count+1) (hbudget : stageSecondCoordinate stage ≤ count)
    (ha : FirstAtom (stageFormula stage)
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
  have hatom : FirstAtom (b 4) (if (b 7).testBit q then moves else moves.drop 1) := by
    simpa [hb4, hb7, q, moves] using ha
  obtain ⟨d5, p5, ht5, hsuffix⟩ := bounded_aligned_first_atom q moves tail b r hb8 hcount hbudget' hb5 hrest hatom
  have haddr : Schedule.scheduledAddress stage = ⟨moves.length+2, b 4, b 7 :: q :: moves⟩ := by
    simp [Schedule.scheduledAddress, Schedule.decodeCoordinates, stageFormula, stageChallenge,
      stageSecondCoordinate, stageRemaining, stageRemainingMoves, hpositive, hb4, hb7, q, moves, Nat.add_assoc]
  rw [hb1, ← haddr] at hsuffix
  have h := hfour.trans graphSystem hsuffix
  have hw : stageFourWord stage ++ (PASoundness.UnaryCodec.encodeFields moves ++
      PASoundness.UnaryCodec.unary (PASoundness.UnaryCodec.bitNat
        (M236Game.selectedValue (Schedule.scheduledAddress stage)))) =
      PASoundness.UnaryCodec.encodeFrame (Schedule.scheduledAddress stage)
        (M236Game.selectedValue (Schedule.scheduledAddress stage)) := by
    rw [← List.append_assoc]
    have hword := stage_overflow_address_word stage count hpositive
    change stageFourWord stage ++ PASoundness.UnaryCodec.encodeFields moves = _ at hword
    rw [hword, encode_fields_boolean_frame]
  rw [hw] at h
  exact ⟨_, _, by omega, h⟩

/-- The finite split discharges the entire successful-budget case: its paid
moves either all time out non-atomically or encounter their first atom. -/
theorem scheduler_bounded_frame (stage count : Nat) (reserve : List Nat)
    (hpositive : (Cantor.unpair stage).1 = count+1) (hbudget : stageSecondCoordinate stage ≤ count) :
    ∃ steps nextReserve, 0 < steps ∧
      graphSystem.Block (cfg 0 BlankFirst.zeros stage 0 0 reserve) steps
        (cfg 0 BlankFirst.zeros (stage+1) 0 0 nextReserve)
        (PASoundness.UnaryCodec.encodeFrame (Schedule.scheduledAddress stage)
          (M236Game.selectedValue (Schedule.scheduledAddress stage))) := by
  rcases finite_first_atom_split (stageFormula stage)
    (if (stageChallenge stage).testBit (stageSecondCoordinate stage) then stageRemainingMoves stage count
     else (stageRemainingMoves stage count).drop 1) with hn | ha
  · exact scheduler_bounded_nonatomic_frame stage count reserve hpositive hbudget hn
  · exact scheduler_bounded_first_atom_frame stage count reserve hpositive hbudget ha

/-- Concrete bounded atomic example: stage 12 evaluates one paid atomic move. -/
theorem stage_twelve_first_atom :
    (Cantor.unpair 12).1 = 1+1 ∧ stageSecondCoordinate 12 ≤ 1 ∧
    FirstAtom (stageFormula 12)
      (if (stageChallenge 12).testBit (stageSecondCoordinate 12) then stageRemainingMoves 12 1
       else (stageRemainingMoves 12 1).drop 1) := by
  constructor
  · simp [Cantor.unpair, Cantor.unpairAux]
  constructor
  · simp [stageSecondCoordinate, stageRemaining, Cantor.unpair, Cantor.unpairAux]
  · refine ⟨[], 0, [], ?_, trivial, ?_⟩
    · simp [stageChallenge, stageSecondCoordinate, stageRemaining, stageRemainingMoves,
        Schedule.decodeCoordinates, Cantor.unpair, Cantor.unpairAux]
    · simp [signedMovesFormula, stageFormula, Cantor.unpair, Cantor.unpairAux]

theorem scheduled_stage_twelve : Schedule.scheduledAddress 12 = ⟨3, 0, [1, 0, 0]⟩ := by
  simp [Schedule.scheduledAddress, Schedule.decodeCoordinates, Cantor.unpair, Cantor.unpairAux]

theorem scheduler_stage_twelve_frame (reserve : List Nat) :
    ∃ steps nextReserve, 0 < steps ∧
      graphSystem.Block (cfg 0 BlankFirst.zeros 12 0 0 reserve) steps
        (cfg 0 BlankFirst.zeros 13 0 0 nextReserve)
        (PASoundness.UnaryCodec.encodeFrame (Schedule.scheduledAddress 12)
          (M236Game.selectedValue (Schedule.scheduledAddress 12))) := by
  exact scheduler_bounded_first_atom_frame 12 1 reserve
    stage_twelve_first_atom.1 stage_twelve_first_atom.2.1 stage_twelve_first_atom.2.2

end PASoundness.M236.OccurrenceGraph
