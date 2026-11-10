import PASoundness.M236AlignedTimeout
import PASoundness.M236SignedAtom

/-! Finite signed non-atomic walks followed by a paid atomic move.
The prepared graph blocks retain explicit alignment and reachability conditions. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

/-- Shared mechanics for a paid atom from a signed evaluator entry. The atom
completion is supplied for the appropriate positive or negative scan. -/
theorem signed_paid_atom_core (start : Nat) (phase : Bool)
    (mr : SignedMoveRows start) (dr : CounterDispatchRows (start+3))
    (ur : UnpairRows (start+3+5)) (er : EmitRows (start+3+5+11))
    (atomFinish : ∀ formula move (base : RegisterMachine.Bank 9) reserve,
      (Cantor.unpair formula).1 = 0 → base 4 = 0 →
      ∃ duration padding, formula+2 ≤ duration ∧
        graphSystem.Block (cfgHalf (start+3+24) base move formula 0 0 reserve) duration
          (cfg 0 BlankFirst.zeros (base 1+1) 0 0 (reserve ++ List.replicate padding 0))
          (PASoundness.UnaryCodec.encodeFields (Schedule.decodeCoordinates (base 3) (base 2)) ++
            PASoundness.UnaryCodec.unary (PASoundness.UnaryCodec.bitNat
              (M236Game.encodedAtom (Cantor.unpair formula).2 (base 5) == phase))))
    (stage count rest env formula : Nat) (reserve : List Nat)
    (htag : (Cantor.unpair formula).1 = 0) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block (cfgExact start (signedWalkBank stage (count+1) rest env formula) reserve) duration
        (cfg 0 BlankFirst.zeros (stage+1) 0 0 (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.unary (Cantor.unpair rest).1 ++
          (PASoundness.UnaryCodec.encodeFields (Schedule.decodeCoordinates count (Cantor.unpair rest).2) ++
            PASoundness.UnaryCodec.unary (PASoundness.UnaryCodec.bitNat
              (M236Game.encodedAtom (Cantor.unpair formula).2 env == phase)))) := by
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
  obtain ⟨d1, p1, hd1, h2⟩ := positive_dispatch_coordinate (start+3) dr ur er T count 0
    (reserve ++ List.replicate formula 0) hs ha hc
  rw [signed_coordinate_to_formula] at h2
  let B := signedCoordinateBank T count
  have ht : B 4 = 0 := by simp [B, signedCoordinateBank, bankAC, bankRest, bankCountTop]
  have hf : T 7 = formula := by simp [T, timeoutBank]
  rw [hf] at h2
  obtain ⟨d2, p2, hd2, h3⟩ := atomFinish formula (Cantor.unpair (T 2)).1 B
    (signedCoordinateReserve T (reserve ++ List.replicate formula 0) p1) htag ht
  have hb1 : B 1 = stage := by simp [B, signedCoordinateBank, bankAC, bankRest, bankCountTop, T, W, timeoutBank, signedWalkBank]
  have hb2 : B 2 = (Cantor.unpair rest).2 := by simp [B, signedCoordinateBank, bankAC, bankRest, T, W, timeoutBank, signedWalkBank]
  have hb3 : B 3 = count := by simp [B, signedCoordinateBank, bankAC, bankRest, bankCountTop]
  have hb5 : B 5 = env := by simp [B, signedCoordinateBank, bankAC, bankRest, bankCountTop, T, W, timeoutBank, signedWalkBank]
  have hr : T 2 = rest := by simp [T, W, timeoutBank, signedWalkBank]
  rw [hb1, hb2, hb3, hb5] at h3
  have h := (h1.trans graphSystem h2).trans graphSystem h3
  refine ⟨(3*formula+1)+(2+(d1+(7*(Cantor.unpair rest).1+3)))+d2,
    formula+1+p1+(Cantor.unpair rest).1+(Cantor.unpair rest).1+p2, by omega, ?_⟩
  have hreserve : signedCoordinateReserve T (reserve ++ List.replicate formula 0) p1 ++ List.replicate p2 0 =
      reserve ++ List.replicate (formula+1+p1+(Cantor.unpair rest).1+(Cantor.unpair rest).1+p2) 0 := by
    simp only [signedCoordinateReserve, hr]
    change (((((reserve ++ List.replicate formula 0) ++ List.replicate 1 0) ++ List.replicate p1 0) ++
      List.replicate (Cantor.unpair rest).1 0) ++ List.replicate (Cantor.unpair rest).1 0) ++ List.replicate p2 0 = _
    simp only [List.append_assoc, ← List.replicate_add]
  rw [hreserve] at h
  simpa [hr] using h

/-- Either signed phase pays an atomic move, emits all remaining fields and
its Boolean payoff, and returns to a clean next-stage boundary. -/
theorem signed_walk_paid_atom (phase : Bool) (stage count rest env formula : Nat)
    (reserve : List Nat) (htag : (Cantor.unpair formula).1 = 0) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block (signedWalkCfg phase stage (count+1) rest env formula reserve) duration
        (cfg 0 BlankFirst.zeros (stage+1) 0 0 (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.unary (Cantor.unpair rest).1 ++
          (PASoundness.UnaryCodec.encodeFields (Schedule.decodeCoordinates count (Cantor.unpair rest).2) ++
            PASoundness.UnaryCodec.unary (PASoundness.UnaryCodec.bitNat
              (M236Game.encodedAtom (Cantor.unpair formula).2 env == phase)))) := by
  cases phase with
  | false =>
    have hf : ∀ formula move (base : RegisterMachine.Bank 9) reserve,
        (Cantor.unpair formula).1 = 0 → base 4 = 0 →
        ∃ duration padding, formula+2 ≤ duration ∧
          graphSystem.Block (cfgHalf (366+3+24) base move formula 0 0 reserve) duration
            (cfg 0 BlankFirst.zeros (base 1+1) 0 0 (reserve ++ List.replicate padding 0))
            (PASoundness.UnaryCodec.encodeFields (Schedule.decodeCoordinates (base 3) (base 2)) ++
              PASoundness.UnaryCodec.unary (PASoundness.UnaryCodec.bitNat
                (M236Game.encodedAtom (Cantor.unpair formula).2 (base 5) == false))) := by
      intro f m b r hf ht
      simpa using signed_atom_positive_finish_393 f m b r hf ht
    simpa [signedWalkCfg, signedWalkIndex] using
      signed_paid_atom_core 366 false signed_move_rows_366 timeout_rows_369 positive_unpair_rows_374
        positive_emit_rows_385 hf stage count rest env formula reserve htag
  | true =>
    have hf : ∀ formula move (base : RegisterMachine.Bank 9) reserve,
        (Cantor.unpair formula).1 = 0 → base 4 = 0 →
        ∃ duration padding, formula+2 ≤ duration ∧
          graphSystem.Block (cfgHalf (546+3+24) base move formula 0 0 reserve) duration
            (cfg 0 BlankFirst.zeros (base 1+1) 0 0 (reserve ++ List.replicate padding 0))
            (PASoundness.UnaryCodec.encodeFields (Schedule.decodeCoordinates (base 3) (base 2)) ++
              PASoundness.UnaryCodec.unary (PASoundness.UnaryCodec.bitNat
                (M236Game.encodedAtom (Cantor.unpair formula).2 (base 5) == true))) := by
      intro f m b r hf ht
      simpa using signed_atom_negative_finish_573 f m b r hf ht
    simpa [signedWalkCfg, signedWalkIndex] using
      signed_paid_atom_core 546 true signed_move_rows_546 signed_dispatch_rows_549 signed_unpair_rows_554
        signed_emit_rows_565 hf stage count rest env formula reserve htag

/-- A finite non-atomic prefix followed by a paid atomic move matches the
abstract signed evaluator, while retaining the exact packed residual tail. -/
theorem signed_walk_first_atom (moves : List Nat) (phase : Bool)
    (stage count paid rest env formula : Nat) (reserve : List Nat)
    (hnonatomic : NonatomicMoves formula moves)
    (hatom : (Cantor.unpair (signedMovesFormula formula moves)).1 = 0) :
    ∃ duration padding, moves.length+1 ≤ duration ∧
      graphSystem.Block
        (signedWalkCfg phase stage ((count+1)+moves.length)
          (Schedule.packCoordinates moves (Cantor.pair paid rest)) env formula reserve) duration
        (cfg 0 BlankFirst.zeros (stage+1) 0 0 (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.encodeFields moves ++
          (PASoundness.UnaryCodec.unary paid ++
            (PASoundness.UnaryCodec.encodeFields (Schedule.decodeCoordinates count rest) ++
              PASoundness.UnaryCodec.unary (PASoundness.UnaryCodec.bitNat
                (!M236Game.encodedPath formula env phase
                  (moves ++ paid :: Schedule.decodeCoordinates count rest)))))) := by
  obtain ⟨d1, p1, hd1, h1⟩ := signed_walk_moves moves phase stage (count+1)
    (Cantor.pair paid rest) env formula reserve hnonatomic
  obtain ⟨d2, p2, hd2, h2⟩ := signed_walk_paid_atom (signedMovesPhase phase moves) stage count
    (Cantor.pair paid rest) (signedMovesEnvironment env moves) (signedMovesFormula formula moves)
    (reserve ++ List.replicate p1 0) hatom
  simp only [Cantor.unpair_pair] at h2
  have hp : (!M236Game.encodedPath formula env phase
      (moves ++ paid :: Schedule.decodeCoordinates count rest)) =
      (M236Game.encodedAtom (Cantor.unpair (signedMovesFormula formula moves)).2
        (signedMovesEnvironment env moves) == signedMovesPhase phase moves) := by
    rw [encoded_path_nonatomic_moves moves (paid :: Schedule.decodeCoordinates count rest)
      phase env formula hnonatomic]
    rw [M236Game.encodedPath]
    simp only [M236Game.tag, hatom, ↓reduceDIte, M236Game.payload]
    cases signedMovesPhase phase moves <;>
      cases M236Game.encodedAtom (Cantor.unpair (signedMovesFormula formula moves)).2
        (signedMovesEnvironment env moves) <;> rfl
  have h := h1.trans graphSystem h2
  refine ⟨d1+d2, p1+p2, by omega, ?_⟩
  have hr : (reserve ++ List.replicate p1 0) ++ List.replicate p2 0 =
      reserve ++ List.replicate (p1+p2) 0 := by
    simp only [List.append_assoc, ← List.replicate_add]
  rw [hr] at h
  rw [hp]
  simpa [List.append_assoc] using h

/-- Row 189 is the initial negative evaluator entry after a zero-bit
alignment; its first atom uses the distinct row-216 scan. -/
theorem signed_189_paid_atom (stage count rest env formula : Nat)
    (reserve : List Nat) (htag : (Cantor.unpair formula).1 = 0) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block (cfgExact 189 (signedWalkBank stage (count+1) rest env formula) reserve) duration
        (cfg 0 BlankFirst.zeros (stage+1) 0 0 (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.unary (Cantor.unpair rest).1 ++
          (PASoundness.UnaryCodec.encodeFields (Schedule.decodeCoordinates count (Cantor.unpair rest).2) ++
            PASoundness.UnaryCodec.unary (PASoundness.UnaryCodec.bitNat
              (M236Game.encodedAtom (Cantor.unpair formula).2 env == true)))) := by
  have hf : ∀ formula move (base : RegisterMachine.Bank 9) reserve,
      (Cantor.unpair formula).1 = 0 → base 4 = 0 →
      ∃ duration padding, formula+2 ≤ duration ∧
        graphSystem.Block (cfgHalf (189+3+24) base move formula 0 0 reserve) duration
          (cfg 0 BlankFirst.zeros (base 1+1) 0 0 (reserve ++ List.replicate padding 0))
          (PASoundness.UnaryCodec.encodeFields (Schedule.decodeCoordinates (base 3) (base 2)) ++
            PASoundness.UnaryCodec.unary (PASoundness.UnaryCodec.bitNat
              (M236Game.encodedAtom (Cantor.unpair formula).2 (base 5) == true))) := by
    intro f m b r hf ht
    simpa using signed_atom_negative_finish_216 f m b r hf ht
  exact signed_paid_atom_core 189 true signed_move_rows_189 signed_dispatch_rows_192
    signed_unpair_rows_197 signed_emit_rows_208 hf stage count rest env formula reserve htag

/-- Entry 189 followed by non-atomic moves and the first paid atom. The
encoded path begins in negative phase even when the prefix is empty. -/
theorem signed_189_first_atom (moves : List Nat) (stage count paid rest env formula : Nat)
    (reserve : List Nat) (hnonatomic : NonatomicMoves formula moves)
    (hatom : (Cantor.unpair (signedMovesFormula formula moves)).1 = 0) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block
        (cfgExact 189 (signedWalkBank stage ((count+1)+moves.length)
          (Schedule.packCoordinates moves (Cantor.pair paid rest)) env formula) reserve) duration
        (cfg 0 BlankFirst.zeros (stage+1) 0 0 (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.encodeFields moves ++
          (PASoundness.UnaryCodec.unary paid ++
            (PASoundness.UnaryCodec.encodeFields (Schedule.decodeCoordinates count rest) ++
              PASoundness.UnaryCodec.unary (PASoundness.UnaryCodec.bitNat
                (!M236Game.encodedPath formula env true
                  (moves ++ paid :: Schedule.decodeCoordinates count rest)))))) := by
  cases moves with
  | nil =>
    obtain ⟨d, p, hd, h⟩ := signed_189_paid_atom stage count (Cantor.pair paid rest) env formula reserve
      (by simpa [signedMovesFormula] using hatom)
    have hp : (!M236Game.encodedPath formula env true (paid :: Schedule.decodeCoordinates count rest)) =
        (M236Game.encodedAtom (Cantor.unpair formula).2 env == true) := by
      rw [M236Game.encodedPath]
      simp only [M236Game.tag, show (Cantor.unpair formula).1 = 0 by simpa [signedMovesFormula] using hatom,
        ↓reduceDIte, M236Game.payload]
      cases M236Game.encodedAtom (Cantor.unpair formula).2 env <;> rfl
    refine ⟨d, p, hd, ?_⟩
    simp only [List.nil_append]
    rw [hp]
    simpa [Schedule.packCoordinates, PASoundness.UnaryCodec.encodeFields] using h
  | cons move moves =>
    have htag : (Cantor.unpair formula).1 ≠ 0 := hnonatomic.1
    have htail : NonatomicMoves (M236Game.child formula move) moves := hnonatomic.2
    have hatom' : (Cantor.unpair (signedMovesFormula (M236Game.child formula move) moves)).1 = 0 := by
      simpa [signedMovesFormula] using hatom
    obtain ⟨d1, p1, hd1, h1⟩ := signed_walk_core 189 366 signed_move_rows_189
      signed_dispatch_rows_192 signed_unpair_rows_197 signed_emit_rows_208 formula_scan_rows_216 formula_branch_row_216
      child_rows_225 pair_env_rows_237 child_next_225 stage ((count+1)+moves.length)
      (Cantor.pair move (Schedule.packCoordinates moves (Cantor.pair paid rest))) env formula reserve htag
    simp only [Cantor.unpair_pair] at h1
    obtain ⟨d2, p2, hd2, h2⟩ := signed_walk_first_atom moves false stage count paid rest
      (Cantor.pair (move-1) env) (M236Game.child formula move)
      (reserve ++ List.replicate p1 0) htail hatom'
    have h := h1.trans graphSystem h2
    refine ⟨d1+d2, p1+p2, by omega, ?_⟩
    have hr : (reserve ++ List.replicate p1 0) ++ List.replicate p2 0 =
        reserve ++ List.replicate (p1+p2) 0 := by
      simp only [List.append_assoc, ← List.replicate_add]
    rw [hr] at h
    rw [show (move :: moves) ++ paid :: Schedule.decodeCoordinates count rest =
      move :: (moves ++ paid :: Schedule.decodeCoordinates count rest) by rfl,
      encoded_nonatomic_clause formula env move true _ htag]
    simpa [signedWalkCfg, signedWalkIndex, Schedule.packCoordinates,
      PASoundness.UnaryCodec.encodeFields, Nat.add_assoc, List.append_assoc] using h

/-- One-bit initial alignment enters the positive phase without consuming an
alignment coordinate. The paid atomic coordinate remains mandatory. -/
theorem aligned_one_first_atom (moves : List Nat) (stage count paid rest env formula : Nat)
    (reserve : List Nat) (hnonatomic : NonatomicMoves formula moves)
    (hatom : (Cantor.unpair (signedMovesFormula formula moves)).1 = 0) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block
        (cfgTimeout 161 (signedWalkBank stage ((count+1)+moves.length)
          (Schedule.packCoordinates moves (Cantor.pair paid rest)) env formula) 1 formula reserve) duration
        (cfg 0 BlankFirst.zeros (stage+1) 0 0 (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.encodeFields moves ++
          (PASoundness.UnaryCodec.unary paid ++
            (PASoundness.UnaryCodec.encodeFields (Schedule.decodeCoordinates count rest) ++
              PASoundness.UnaryCodec.unary (PASoundness.UnaryCodec.bitNat
                (!M236Game.encodedPath formula env false
                  (moves ++ paid :: Schedule.decodeCoordinates count rest)))))) := by
  have h1 := aligned_one_enter stage ((count+1)+moves.length)
    (Schedule.packCoordinates moves (Cantor.pair paid rest)) env formula reserve
  obtain ⟨d, p, hd, h2⟩ := signed_walk_first_atom moves false stage count paid rest env formula
    (reserve ++ [0]) hnonatomic hatom
  have h := h1.trans graphSystem h2
  refine ⟨2+d, 1+p, by omega, ?_⟩
  have hr : (reserve ++ [0]) ++ List.replicate p 0 = reserve ++ List.replicate (1+p) 0 := by
    change (reserve ++ List.replicate 1 0) ++ List.replicate p 0 = _
    simp only [List.append_assoc, ← List.replicate_add]
  rw [hr] at h
  simpa using h

/-- Zero-bit alignment emits one coordinate without evaluating it, then
starts the negative-phase walk. That alignment does not satisfy the paid atom
requirement; a further coordinate must be present. -/
theorem aligned_zero_first_atom (alignment : Nat) (moves : List Nat)
    (stage count paid rest env formula : Nat) (reserve : List Nat)
    (hnonatomic : NonatomicMoves formula moves)
    (hatom : (Cantor.unpair (signedMovesFormula formula moves)).1 = 0) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block
        (cfgTimeout 161 (signedWalkBank stage (((count+1)+moves.length)+1)
          (Schedule.packCoordinates (alignment :: moves) (Cantor.pair paid rest)) env formula) 0 formula reserve) duration
        (cfg 0 BlankFirst.zeros (stage+1) 0 0 (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.unary alignment ++ (PASoundness.UnaryCodec.encodeFields moves ++
          (PASoundness.UnaryCodec.unary paid ++
            (PASoundness.UnaryCodec.encodeFields (Schedule.decodeCoordinates count rest) ++
              PASoundness.UnaryCodec.unary (PASoundness.UnaryCodec.bitNat
                (!M236Game.encodedPath formula env true
                  (moves ++ paid :: Schedule.decodeCoordinates count rest))))))) := by
  let N := (count+1)+moves.length
  let W := signedWalkBank stage (N+1)
    (Cantor.pair alignment (Schedule.packCoordinates moves (Cantor.pair paid rest))) env formula
  have h0 : W 0 = 0 := by simp [W, signedWalkBank]
  have hn : W 3 = N+1 := by simp [W, signedWalkBank]
  have ha : W 6 = 0 := by simp [W, signedWalkBank]
  have hc : W 8 = 0 := by simp [W, signedWalkBank]
  obtain ⟨d1, p1, hd1, h1⟩ := positive_zero_to_189 W N formula reserve h0 hn ha hc
  have hview : positiveZeroExit W N formula reserve p1 =
      cfgExact 189 (signedWalkBank stage N (Schedule.packCoordinates moves (Cantor.pair paid rest)) env formula)
        (reserve ++ List.replicate (1+p1+alignment+alignment+alignment) 0) := by
    have hr : (((((reserve ++ [0]) ++ List.replicate p1 0) ++ List.replicate alignment 0) ++
        List.replicate alignment 0) ++ List.replicate alignment 0) =
        reserve ++ List.replicate (1+p1+alignment+alignment+alignment) 0 := by
      change (((((reserve ++ List.replicate 1 0) ++ List.replicate p1 0) ++ List.replicate alignment 0) ++
        List.replicate alignment 0) ++ List.replicate alignment 0) = _
      simp only [List.append_assoc, ← List.replicate_add]
    unfold positiveZeroExit cfgAS cfgExact
    simp only [show W 2 = Cantor.pair alignment (Schedule.packCoordinates moves (Cantor.pair paid rest)) by simp [W, signedWalkBank],
      Cantor.unpair_pair]
    rw [hr]
    congr 1
    funext j
    fin_cases j <;> simp [bankAS, bankAC, bankRest, bankCountTop, timeoutBank, W, signedWalkBank]
  rw [hview] at h1
  obtain ⟨d2, p2, hd2, h2⟩ := signed_189_first_atom moves stage count paid rest env formula
    (reserve ++ List.replicate (1+p1+alignment+alignment+alignment) 0) hnonatomic hatom
  have h := h1.trans graphSystem h2
  refine ⟨(1+(2+(d1+(7*alignment+3))))+(2*alignment+1)+d2,
    (1+p1+alignment+alignment+alignment)+p2, by omega, ?_⟩
  have hr : (reserve ++ List.replicate (1+p1+alignment+alignment+alignment) 0) ++ List.replicate p2 0 =
      reserve ++ List.replicate ((1+p1+alignment+alignment+alignment)+p2) 0 := by
    simp only [List.append_assoc, ← List.replicate_add]
  rw [hr] at h
  simpa [N, W, signedWalkBank, Schedule.packCoordinates, Cantor.unpair_pair, List.append_assoc] using h

/-- At a well-budgeted positive alignment, the emitted signed-path payoff is
the selected source value. This is an abstract equality, independent of graph
reachability. -/
theorem selected_first_atom_one_value (formula challenge y : Nat) (moves : List Nat)
    (hy : y ≤ moves.length) (hbit : challenge.testBit y = true) :
    M236Game.selectedValue ⟨moves.length+2, formula, challenge :: y :: moves⟩ =
      (!M236Game.encodedPath formula (Cantor.pair y 0) false moves) := by
  rw [← M236Game.selected_encoded_value]
  simp [M236Game.selectedEncodedValue, M236Game.encodedAligned, hbit, Nat.not_lt_of_ge hy]

/-- At a well-budgeted zero alignment, the first coordinate is ignored by
the evaluator and the rest starts in negative phase. -/
theorem selected_first_atom_zero_value (formula challenge y alignment : Nat) (moves : List Nat)
    (hy : y ≤ (alignment :: moves).length) (hbit : challenge.testBit y = false) :
    M236Game.selectedValue ⟨(alignment :: moves).length+2, formula, challenge :: y :: alignment :: moves⟩ =
      (!M236Game.encodedPath formula (Cantor.pair y 0) true moves) := by
  have hy' : y ≤ moves.length+1 := by simpa using hy
  rw [← M236Game.selected_encoded_value]
  simp [M236Game.selectedEncodedValue, M236Game.encodedAligned, hbit, Nat.not_lt_of_ge hy']

/-- Prepared one-bit path emitting the corresponding selected source payoff. -/
theorem aligned_one_first_atom_selected (moves : List Nat) (stage count paid rest formula challenge y : Nat)
    (reserve : List Nat) (hnonatomic : NonatomicMoves formula moves)
    (hatom : (Cantor.unpair (signedMovesFormula formula moves)).1 = 0)
    (hy : y ≤ (moves ++ paid :: Schedule.decodeCoordinates count rest).length)
    (hbit : challenge.testBit y = true) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block
        (cfgTimeout 161 (signedWalkBank stage ((count+1)+moves.length)
          (Schedule.packCoordinates moves (Cantor.pair paid rest)) (Cantor.pair y 0) formula) 1 formula reserve) duration
        (cfg 0 BlankFirst.zeros (stage+1) 0 0 (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.encodeFields moves ++
          (PASoundness.UnaryCodec.unary paid ++
            (PASoundness.UnaryCodec.encodeFields (Schedule.decodeCoordinates count rest) ++
              PASoundness.UnaryCodec.unary (PASoundness.UnaryCodec.bitNat
                (M236Game.selectedValue ⟨(moves ++ paid :: Schedule.decodeCoordinates count rest).length+2,
                  formula, challenge :: y :: (moves ++ paid :: Schedule.decodeCoordinates count rest)⟩))))) := by
  obtain ⟨d, p, hd, h⟩ := aligned_one_first_atom moves stage count paid rest (Cantor.pair y 0) formula
    reserve hnonatomic hatom
  refine ⟨d, p, hd, ?_⟩
  rw [selected_first_atom_one_value formula challenge y _ hy hbit]
  exact h

/-- Prepared zero-bit path: the separately emitted alignment coordinate is
present in the selected address but excluded from the signed evaluator. -/
theorem aligned_zero_first_atom_selected (alignment : Nat) (moves : List Nat)
    (stage count paid rest formula challenge y : Nat) (reserve : List Nat)
    (hnonatomic : NonatomicMoves formula moves)
    (hatom : (Cantor.unpair (signedMovesFormula formula moves)).1 = 0)
    (hy : y ≤ (alignment :: (moves ++ paid :: Schedule.decodeCoordinates count rest)).length)
    (hbit : challenge.testBit y = false) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block
        (cfgTimeout 161 (signedWalkBank stage (((count+1)+moves.length)+1)
          (Schedule.packCoordinates (alignment :: moves) (Cantor.pair paid rest)) (Cantor.pair y 0) formula) 0 formula reserve) duration
        (cfg 0 BlankFirst.zeros (stage+1) 0 0 (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.unary alignment ++ (PASoundness.UnaryCodec.encodeFields moves ++
          (PASoundness.UnaryCodec.unary paid ++
            (PASoundness.UnaryCodec.encodeFields (Schedule.decodeCoordinates count rest) ++
              PASoundness.UnaryCodec.unary (PASoundness.UnaryCodec.bitNat
                (M236Game.selectedValue ⟨(alignment :: (moves ++ paid :: Schedule.decodeCoordinates count rest)).length+2,
                  formula, challenge :: y :: alignment :: (moves ++ paid :: Schedule.decodeCoordinates count rest)⟩)))))) := by
  obtain ⟨d, p, hd, h⟩ := aligned_zero_first_atom alignment moves stage count paid rest (Cantor.pair y 0)
    formula reserve hnonatomic hatom
  refine ⟨d, p, hd, ?_⟩
  rw [selected_first_atom_zero_value formula challenge y alignment _ hy hbit]
  exact h

end PASoundness.M236.OccurrenceGraph
