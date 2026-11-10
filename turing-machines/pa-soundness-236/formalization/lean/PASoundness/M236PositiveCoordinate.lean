import PASoundness.M236BoundedTimeout

/-! Positive-count coordinate dispatch in both literal polarity branches. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

theorem positive_unpair_rows_168 : UnpairRows 168 := by constructor <;> decide
theorem positive_unpair_rows_374 : UnpairRows 374 := by constructor <;> decide
theorem positive_emit_rows_179 : EmitRows 179 := by constructor <;> decide
theorem positive_emit_rows_385 : EmitRows 385 := by constructor <;> decide

/-- The count/top view and the unpairing view coincide at any index with
clean a and c registers. -/
theorem coordinate_count_top_to_unpair (i : Nat) (base : RegisterMachine.Bank 9)
    (count top : Nat) (reserve : List Nat) (ha : base 6 = 0) (hc : base 8 = 0) :
    cfgCountTop i base count top reserve =
      cfgRAC i (bankCountTop base count top) (base 2) 0 0 reserve := by
  unfold cfgCountTop cfgRAC cfgAC
  congr 1
  funext j
  fin_cases j <;> simp [bankCountTop, bankAC, bankRest, ha, hc]

def positiveCoordinateExit (k : Nat) (base : RegisterMachine.Bank 9) (count top : Nat)
    (reserve : List Nat) (padding : Nat) : GraphState :=
  let q := (Cantor.unpair (base 2)).1
  cfgAS ((k+5+11)+8)
    (bankAC (bankRest (bankCountTop base count top) (Cantor.unpair (base 2)).2) q 0) q 0
    ((((reserve ++ [0]) ++ List.replicate padding 0) ++ List.replicate q 0) ++ List.replicate q 0)

/-- At either checked positive-count dispatch, decrement the counter, split the
packed remainder and emit exactly one unary coordinate. The full bank and
reserve, including the retained top register, are explicit in the endpoint. -/
theorem positive_dispatch_coordinate (k : Nat) (dr : CounterDispatchRows k)
    (ur : UnpairRows (k+5)) (er : EmitRows (k+5+11))
    (base : RegisterMachine.Bank 9) (count top : Nat) (reserve : List Nat)
    (hs : base 0 = 0) (ha : base 6 = 0) (hc : base 8 = 0) :
    ∃ duration padding, base 2 + 1 ≤ duration ∧
      graphSystem.Block (cfgCountTop k base (count+1) top reserve)
        (2+(duration+(7*(Cantor.unpair (base 2)).1+3)))
        (positiveCoordinateExit k base count top reserve padding)
        (PASoundness.UnaryCodec.unary (Cantor.unpair (base 2)).1) := by
  have h1 := counter_dispatch_positive k dr base count top reserve
  rw [coordinate_count_top_to_unpair (k+5) base count top (reserve ++ [0]) ha hc] at h1
  have hs' : bankCountTop base count top 0 = 0 := by simp [bankCountTop, hs]
  obtain ⟨duration, padding, ht, h2⟩ :=
    generic_unpair_then_emit (base 2) (k+5) ur er (bankCountTop base count top) (reserve ++ [0]) hs'
  refine ⟨duration, padding, ht, ?_⟩
  simpa [positiveCoordinateExit] using h1.trans graphSystem h2

/-- The row 163 branch emits one coordinate and arrives at row 187. -/
theorem positive_dispatch_coordinate_163 (base : RegisterMachine.Bank 9) (count top : Nat)
    (reserve : List Nat) (hs : base 0 = 0) (ha : base 6 = 0) (hc : base 8 = 0) :
    ∃ duration padding, base 2 + 1 ≤ duration ∧
      graphSystem.Block (cfgCountTop 163 base (count+1) top reserve)
        (2+(duration+(7*(Cantor.unpair (base 2)).1+3)))
        (positiveCoordinateExit 163 base count top reserve padding)
        (PASoundness.UnaryCodec.unary (Cantor.unpair (base 2)).1) := by
  exact positive_dispatch_coordinate 163 timeout_rows_163 positive_unpair_rows_168 positive_emit_rows_179
    base count top reserve hs ha hc

/-- The row 369 branch emits one coordinate and arrives at row 393. -/
theorem positive_dispatch_coordinate_369 (base : RegisterMachine.Bank 9) (count top : Nat)
    (reserve : List Nat) (hs : base 0 = 0) (ha : base 6 = 0) (hc : base 8 = 0) :
    ∃ duration padding, base 2 + 1 ≤ duration ∧
      graphSystem.Block (cfgCountTop 369 base (count+1) top reserve)
        (2+(duration+(7*(Cantor.unpair (base 2)).1+3)))
        (positiveCoordinateExit 369 base count top reserve padding)
        (PASoundness.UnaryCodec.unary (Cantor.unpair (base 2)).1) := by
  exact positive_dispatch_coordinate 369 timeout_rows_369 positive_unpair_rows_374 positive_emit_rows_385
    base count top reserve hs ha hc

/-- The one-bit branch moves the saved top into b, decrements the positive
counter, emits the next coordinate, and reaches row 393. -/
theorem positive_one_to_393 (base : RegisterMachine.Bank 9) (count top : Nat) (reserve : List Nat)
    (hs : base 0 = 0) (hcount : base 3 = count+1)
    (ha : base 6 = 0) (hc : base 8 = 0) :
    ∃ duration padding, base 2+1 ≤ duration ∧
      graphSystem.Block (cfgTimeout 161 base 1 top reserve)
        ((3*top+3)+(2+(duration+(7*(Cantor.unpair (base 2)).1+3))))
        (positiveCoordinateExit 369 (timeoutBank base top 0) count 0
          ((reserve ++ [0]) ++ List.replicate top 0) padding)
        (PASoundness.UnaryCodec.unary (Cantor.unpair (base 2)).1) := by
  have h1 := WordEventSystem.Block.single graphSystem (timeout_bit_one base top reserve)
  have h2 := WordEventSystem.Block.single graphSystem (timeout_jump162 base 0 top (reserve ++ [0]))
  have h3 := timeout_move_top top base 0 (reserve ++ [0])
  simp only [Nat.zero_add] at h3
  rw [timeout_count_view 369 base top 0 _, hcount] at h3
  have hs' : timeoutBank base top 0 0 = 0 := by simp [timeoutBank, hs]
  have ha' : timeoutBank base top 0 6 = 0 := by simp [timeoutBank, ha]
  have hc' : timeoutBank base top 0 8 = 0 := by simp [timeoutBank, hc]
  obtain ⟨duration, padding, ht, h4⟩ := positive_dispatch_coordinate_369
    (timeoutBank base top 0) count 0 ((reserve ++ [0]) ++ List.replicate top 0) hs' ha' hc'
  have h := ((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4
  refine ⟨duration, padding, by simpa [timeoutBank] using ht, ?_⟩
  have htime : 1+1+(3*top+1)+(2+(duration+(7*(Cantor.unpair (base 2)).1+3))) =
      (3*top+3)+(2+(duration+(7*(Cantor.unpair (base 2)).1+3))) := by omega
  simpa [htime, timeoutBank] using h

/-- The row-393 endpoint retains the full named register interface. -/
theorem positive_one_exit_registers (base : RegisterMachine.Bank 9) (count top : Nat)
    (reserve : List Nat) (padding : Nat) :
    let s := positiveCoordinateExit 369 (timeoutBank base top 0) count 0 reserve padding
    s.index = 393 ∧ s.registers 0 = 0 ∧ s.registers 1 = base 1 ∧
    s.registers 2 = (Cantor.unpair (base 2)).2 ∧ s.registers 3 = count ∧
    s.registers 4 = 0 ∧ s.registers 5 = base 5 ∧
    s.registers 6 = (Cantor.unpair (base 2)).1 ∧ s.registers 7 = top ∧ s.registers 8 = 0 := by
  simp [positiveCoordinateExit, cfgAS, bankAS, bankAC, bankRest, bankCountTop, timeoutBank]

/-- Physical lift conditional on the selected run reaching the prepared
row-161 one-bit state with positive count. -/
theorem selected_positive_one_to_393 (i : Nat) (base : RegisterMachine.Bank 9)
    (count top : Nat) (reserve : List Nat) (hs : base 0 = 0) (hcount : base 3 = count+1)
    (ha : base 6 = 0) (hc : base 8 = 0)
    (h : graphSystem.run i = cfgTimeout 161 base 1 top reserve) :
    ∃ duration padding finish, base 2+1 ≤ duration ∧ Good finish ∧
      finish.graphState = positiveCoordinateExit 369 (timeoutBank base top 0) count 0
        ((reserve ++ [0]) ++ List.replicate top 0) padding ∧
      graphSystem.run (i+((3*top+3)+(2+(duration+(7*(Cantor.unpair (base 2)).1+3))))) =
        positiveCoordinateExit 369 (timeoutBank base top 0) count 0
          ((reserve ++ [0]) ++ List.replicate top 0) padding ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i+((3*top+3)+(2+(duration+(7*(Cantor.unpair (base 2)).1+3)))))) ∧
      (machineWordSystem machine machineLabels).prefixWord
          (graphRefinement.boundary (i+((3*top+3)+(2+(duration+(7*(Cantor.unpair (base 2)).1+3)))))) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++
          PASoundness.UnaryCodec.unary (Cantor.unpair (base 2)).1 ∧
      graphRefinement.boundary i <
        graphRefinement.boundary (i+((3*top+3)+(2+(duration+(7*(Cantor.unpair (base 2)).1+3))))) := by
  obtain ⟨duration, padding, ht, block⟩ := positive_one_to_393 base count top reserve hs hcount ha hc
  have hr : graphSystem.run (i+((3*top+3)+(2+(duration+(7*(Cantor.unpair (base 2)).1+3))))) =
      positiveCoordinateExit 369 (timeoutBank base top 0) count 0
        ((reserve ++ [0]) ++ List.replicate top 0) padding := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i+((3*top+3)+(2+(duration+(7*(Cantor.unpair (base 2)).1+3))))) =
      graphSystem.prefixWord i ++ PASoundness.UnaryCodec.unary (Cantor.unpair (base 2)).1 := by
    rw [WordEventSystem.prefix_add, h, block.output]
  obtain ⟨finish, hg, hstate, hconfig⟩ := graphRefinement.related
    (i+((3*top+3)+(2+(duration+(7*(Cantor.unpair (base 2)).1+3)))))
  refine ⟨duration, padding, finish, ht, hg, hstate.trans hr, hr, hconfig, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

theorem positive_row187 : sourceRows[187]? = some ("3.k.a.decnz", 188, some 189) := by decide
theorem positive_row188 : sourceRows[188]? = some ("jump", 187, none) := by decide

theorem positive_clear_dec (base : RegisterMachine.Bank 9) (n scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAS 187 base (n+1) scratch reserve) =
      (cfgAS 188 base n scratch (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgAS, positive_row187, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAS, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankAS, RegisterMachine.write])

theorem positive_clear_zero (base : RegisterMachine.Bank 9) (scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAS 187 base 0 scratch reserve) = (cfgAS 189 base 0 scratch reserve, []) := by
  simp [graphSystem, graphNext, cfgAS, positive_row187, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAS, RegisterMachine.execute]

theorem positive_clear_jump (base : RegisterMachine.Bank 9) (a scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAS 188 base a scratch reserve) = (cfgAS 187 base a scratch reserve, []) := by
  simp [graphSystem, graphNext, cfgAS, positive_row188, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

theorem positive_clear_alignment (n : Nat) (base : RegisterMachine.Bank 9) (scratch : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgAS 187 base n scratch reserve) (2*n+1)
      (cfgAS 189 base 0 scratch (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing reserve with
  | zero => simpa using WordEventSystem.Block.single graphSystem (positive_clear_zero base scratch reserve)
  | succ n ih =>
    have h1 := WordEventSystem.Block.single graphSystem (positive_clear_dec base n scratch reserve)
    have h2 := WordEventSystem.Block.single graphSystem (positive_clear_jump base n scratch (reserve ++ [0]))
    have h := (h1.trans graphSystem h2).trans graphSystem (ih (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

def positiveZeroExit (base : RegisterMachine.Bank 9) (count top : Nat) (reserve : List Nat) (padding : Nat) : GraphState :=
  let v := timeoutBank base 0 top
  let q := (Cantor.unpair (base 2)).1
  let B := bankAC (bankRest (bankCountTop v count top) (Cantor.unpair (base 2)).2) q 0
  cfgAS 189 B 0 0
    (((((reserve ++ [0]) ++ List.replicate padding 0) ++ List.replicate q 0) ++ List.replicate q 0) ++ List.replicate q 0)

/-- The zero-bit branch emits an alignment coordinate, clears that coordinate
from a, and reaches row 189 with the saved top retained. -/
theorem positive_zero_to_189 (base : RegisterMachine.Bank 9) (count top : Nat) (reserve : List Nat)
    (hs : base 0 = 0) (hcount : base 3 = count+1)
    (ha : base 6 = 0) (hc : base 8 = 0) :
    ∃ duration padding, base 2+1 ≤ duration ∧
      graphSystem.Block (cfgTimeout 161 base 0 top reserve)
        ((1+(2+(duration+(7*(Cantor.unpair (base 2)).1+3))))+(2*(Cantor.unpair (base 2)).1+1))
        (positiveZeroExit base count top reserve padding)
        (PASoundness.UnaryCodec.unary (Cantor.unpair (base 2)).1) := by
  have h1 := WordEventSystem.Block.single graphSystem (timeout_bit_zero base top reserve)
  rw [timeout_count_view 163 base 0 top reserve, hcount] at h1
  have hs' : timeoutBank base 0 top 0 = 0 := by simp [timeoutBank, hs]
  have ha' : timeoutBank base 0 top 6 = 0 := by simp [timeoutBank, ha]
  have hc' : timeoutBank base 0 top 8 = 0 := by simp [timeoutBank, hc]
  obtain ⟨duration, padding, ht, h2⟩ := positive_dispatch_coordinate_163
    (timeoutBank base 0 top) count top reserve hs' ha' hc'
  let q := (Cantor.unpair (base 2)).1
  let B := bankAC (bankRest (bankCountTop (timeoutBank base 0 top) count top) (Cantor.unpair (base 2)).2) q 0
  let r := (((reserve ++ [0]) ++ List.replicate padding 0) ++ List.replicate q 0) ++ List.replicate q 0
  change graphSystem.Block (cfgCountTop 163 (timeoutBank base 0 top) (count+1) top reserve) _
    (cfgAS 187 B q 0 r) _ at h2
  have h3 := positive_clear_alignment q B 0 r
  have h := (h1.trans graphSystem h2).trans graphSystem h3
  refine ⟨duration, padding, by simpa [timeoutBank] using ht, ?_⟩
  simpa [positiveZeroExit, q, B, r, timeoutBank, Nat.add_assoc] using h

/-- The zero-bit alignment exit preserves the exact remaining-register values. -/
theorem positive_zero_exit_registers (base : RegisterMachine.Bank 9) (count top : Nat)
    (reserve : List Nat) (padding : Nat) :
    let s := positiveZeroExit base count top reserve padding
    s.index = 189 ∧ s.registers 0 = 0 ∧ s.registers 1 = base 1 ∧
    s.registers 2 = (Cantor.unpair (base 2)).2 ∧ s.registers 3 = count ∧
    s.registers 4 = top ∧ s.registers 5 = base 5 ∧
    s.registers 6 = 0 ∧ s.registers 7 = 0 ∧ s.registers 8 = 0 := by
  simp [positiveZeroExit, cfgAS, bankAS, bankAC, bankRest, bankCountTop, timeoutBank]

/-- Physical lift of the zero-bit alignment path at a reached prepared entry. -/
theorem selected_positive_zero_to_189 (i : Nat) (base : RegisterMachine.Bank 9)
    (count top : Nat) (reserve : List Nat) (hs : base 0 = 0) (hcount : base 3 = count+1)
    (ha : base 6 = 0) (hc : base 8 = 0)
    (h : graphSystem.run i = cfgTimeout 161 base 0 top reserve) :
    ∃ duration padding finish, base 2+1 ≤ duration ∧ Good finish ∧
      finish.graphState = positiveZeroExit base count top reserve padding ∧
      graphSystem.run (i+((1+(2+(duration+(7*(Cantor.unpair (base 2)).1+3))))+(2*(Cantor.unpair (base 2)).1+1))) =
        positiveZeroExit base count top reserve padding ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i+((1+(2+(duration+(7*(Cantor.unpair (base 2)).1+3))))+(2*(Cantor.unpair (base 2)).1+1)))) ∧
      (machineWordSystem machine machineLabels).prefixWord
          (graphRefinement.boundary (i+((1+(2+(duration+(7*(Cantor.unpair (base 2)).1+3))))+(2*(Cantor.unpair (base 2)).1+1)))) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++
          PASoundness.UnaryCodec.unary (Cantor.unpair (base 2)).1 ∧
      graphRefinement.boundary i < graphRefinement.boundary
        (i+((1+(2+(duration+(7*(Cantor.unpair (base 2)).1+3))))+(2*(Cantor.unpair (base 2)).1+1))) := by
  obtain ⟨duration, padding, ht, block⟩ := positive_zero_to_189 base count top reserve hs hcount ha hc
  have hr : graphSystem.run (i+((1+(2+(duration+(7*(Cantor.unpair (base 2)).1+3))))+(2*(Cantor.unpair (base 2)).1+1))) =
      positiveZeroExit base count top reserve padding := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i+((1+(2+(duration+(7*(Cantor.unpair (base 2)).1+3))))+(2*(Cantor.unpair (base 2)).1+1))) =
      graphSystem.prefixWord i ++ PASoundness.UnaryCodec.unary (Cantor.unpair (base 2)).1 := by
    rw [WordEventSystem.prefix_add, h, block.output]
  obtain ⟨finish, hg, hstate, hconfig⟩ := graphRefinement.related
    (i+((1+(2+(duration+(7*(Cantor.unpair (base 2)).1+3))))+(2*(Cantor.unpair (base 2)).1+1)))
  refine ⟨duration, padding, finish, ht, hg, hstate.trans hr, hr, hconfig, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

def boundedInitializedBank (base : RegisterMachine.Bank 9) (n : Nat) : RegisterMachine.Bank 9 :=
  bankBudget (boundedBitBank base n) (base 3) (Cantor.pair (base 5+n) 0) 0 0

/-- The successful bounded initialization followed by the selected-one path
emits the next coordinate and reaches row 393. All entry conditions are
explicit; in particular, the indexed bit must be one and the remaining count
must be positive. -/
theorem bounded_initialization_one_to_393 (n remaining : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hc : base 8 = 0) (hcount : base 3 = remaining+1)
    (hbudget : n ≤ remaining+1) (hbit : (base 7).testBit n = true) :
    ∃ initDuration initPadding coordDuration coordPadding,
      n+2 ≤ initDuration ∧ base 2+1 ≤ coordDuration ∧
      graphSystem.Block (cfgAS 103 base n 0 reserve)
        (((10*n+2)+initDuration) +
          ((3*(base 4)+3)+(2+(coordDuration+(7*(Cantor.unpair (base 2)).1+3)))))
        (positiveCoordinateExit 369 (timeoutBank (boundedInitializedBank base n) (base 4) 0) remaining 0
          (((reserve ++ List.replicate (3*n+initPadding) 0) ++ [0]) ++ List.replicate (base 4) 0) coordPadding)
        (PASoundness.UnaryCodec.unary (Cantor.unpair (base 2)).1) := by
  have hcount' : base 3 = (remaining+1-n)+n := by omega
  obtain ⟨d1, p1, hd1, h1⟩ := budget_success_then_initialize n (remaining+1-n) base reserve hc hcount'
  let B := boundedInitializedBank base n
  let r := reserve ++ List.replicate (3*n+p1) 0
  have hview : cfgBudget 161 (boundedBitBank base n) (base 3) (Cantor.pair (base 5+n) 0) 0 0 r =
      cfgTimeout 161 B 1 (base 4) r := by
    unfold cfgBudget cfgTimeout
    congr 1
    funext i
    fin_cases i <;> simp [B, boundedInitializedBank, boundedBitBank, bankBudget, bankHalf, bankAS, timeoutBank, hbit]
  rw [hview] at h1
  have hs' : B 0 = 0 := by simp [B, boundedInitializedBank, boundedBitBank, bankBudget, bankHalf]
  have hn' : B 3 = remaining+1 := by simp [B, boundedInitializedBank, bankBudget, hcount]
  have ha' : B 6 = 0 := by simp [B, boundedInitializedBank, bankBudget]
  have hc' : B 8 = 0 := by simp [B, boundedInitializedBank, bankBudget]
  obtain ⟨d2, p2, hd2, h2⟩ := positive_one_to_393 B remaining (base 4) r hs' hn' ha' hc'
  have h := h1.trans graphSystem h2
  refine ⟨d1, p1, d2, p2, hd1, ?_, ?_⟩
  · simpa [B, boundedInitializedBank, boundedBitBank, bankBudget, bankHalf, bankAS] using hd2
  · simpa [B, r, boundedInitializedBank, boundedBitBank, bankBudget, bankHalf, bankAS] using h


/-- The successful bounded initialization followed by the selected-zero path
emits the next coordinate and reaches row 189. All entry conditions are
explicit; in particular, the indexed bit must be zero and the remaining count
must be positive. -/
theorem bounded_initialization_zero_to_189 (n remaining : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hc : base 8 = 0) (hcount : base 3 = remaining+1)
    (hbudget : n ≤ remaining+1) (hbit : (base 7).testBit n = false) :
    ∃ initDuration initPadding coordDuration coordPadding,
      n+2 ≤ initDuration ∧ base 2+1 ≤ coordDuration ∧
      graphSystem.Block (cfgAS 103 base n 0 reserve)
        (((10*n+2)+initDuration) +
          ((1+(2+(coordDuration+(7*(Cantor.unpair (base 2)).1+3))))+(2*(Cantor.unpair (base 2)).1+1)))
        (positiveZeroExit (boundedInitializedBank base n) remaining (base 4)
          (reserve ++ List.replicate (3*n+initPadding) 0) coordPadding)
        (PASoundness.UnaryCodec.unary (Cantor.unpair (base 2)).1) := by
  have hcount' : base 3 = (remaining+1-n)+n := by omega
  obtain ⟨d1, p1, hd1, h1⟩ := budget_success_then_initialize n (remaining+1-n) base reserve hc hcount'
  let B := boundedInitializedBank base n
  let r := reserve ++ List.replicate (3*n+p1) 0
  have hview : cfgBudget 161 (boundedBitBank base n) (base 3) (Cantor.pair (base 5+n) 0) 0 0 r =
      cfgTimeout 161 B 0 (base 4) r := by
    unfold cfgBudget cfgTimeout
    congr 1
    funext i
    fin_cases i <;> simp [B, boundedInitializedBank, boundedBitBank, bankBudget, bankHalf, bankAS, timeoutBank, hbit]
  rw [hview] at h1
  have hs' : B 0 = 0 := by simp [B, boundedInitializedBank, boundedBitBank, bankBudget, bankHalf]
  have hn' : B 3 = remaining+1 := by simp [B, boundedInitializedBank, bankBudget, hcount]
  have ha' : B 6 = 0 := by simp [B, boundedInitializedBank, bankBudget]
  have hc' : B 8 = 0 := by simp [B, boundedInitializedBank, bankBudget]
  obtain ⟨d2, p2, hd2, h2⟩ := positive_zero_to_189 B remaining (base 4) r hs' hn' ha' hc'
  have h := h1.trans graphSystem h2
  refine ⟨d1, p1, d2, p2, hd1, ?_, ?_⟩
  · simpa [B, boundedInitializedBank, boundedBitBank, bankBudget, bankHalf, bankAS] using hd2
  · simpa [B, r, boundedInitializedBank, boundedBitBank, bankBudget, bankHalf, bankAS] using h

end PASoundness.M236.OccurrenceGraph
