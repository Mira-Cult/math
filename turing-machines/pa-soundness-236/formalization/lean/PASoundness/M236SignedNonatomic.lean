import PASoundness.M236ChildSelect

/-! Non-atomic local evaluator steps at the three checked signed occurrences. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

/-- A checked formula-scan, positive-tag selector, environment pairing and
continuation implement one prepared non-atomic step. Zero initial top and a
nonzero tag are explicit. This local graph block is silent and retains every
register not shown as modified. -/
theorem signed_nonatomic_step (k dest : Nat) (scan : FormulaScanRows k) (branch : FormulaBranchRow k)
    (select : ChildSelectRows (k+9)) (pairRows : PairEnvRows (k+9+12)) (next : ChildNextRow (k+9) dest)
    (formula move : Nat) (base : RegisterMachine.Bank 9) (reserve : List Nat)
    (htag : (Cantor.unpair formula).1 ≠ 0) (htop : base 4 = 0) :
    ∃ duration padding, formula+2 ≤ duration ∧
      graphSystem.Block (cfgHalf k base move formula 0 0 reserve) duration
        (cfgBudget dest (bankSelect base (move-1) 0 0 0 (M236Game.child formula move))
          (base 3) (Cantor.pair (move-1) (base 5)) 0 0 (reserve ++ List.replicate padding 0)) [] := by
  have htag' : (Cantor.unpair formula).1 = ((Cantor.unpair formula).1-1)+1 := by omega
  obtain ⟨d1, p1, hd1, h1⟩ := formula_unpair_positive_branch move formula k
    ((Cantor.unpair formula).1-1) scan branch base reserve htag'
  rw [half_to_child_view (k+9) base move 0 ((Cantor.unpair formula).1-1) (Cantor.unpair formula).2 _, htop] at h1
  obtain ⟨d2, p2, hd2, h2⟩ := child_select_pair_continue (k+9) dest select pairRows next base move 0
    ((Cantor.unpair formula).1-1) (Cantor.unpair formula).2 0 (reserve ++ List.replicate p1 0)
  have h := h1.trans graphSystem h2
  refine ⟨d1+d2, p1+p2, by omega, ?_⟩
  have hr : (reserve ++ List.replicate p1 0) ++ List.replicate p2 0 =
      reserve ++ List.replicate (p1+p2) 0 := by
    simp only [List.append_assoc, ← List.replicate_add]
  rw [hr] at h
  simpa [child_choice_eq_abstract] using h

/-- First checked negative-phase occurrence, including its continuation row. -/
theorem signed_nonatomic_216 (formula move : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (htag : (Cantor.unpair formula).1 ≠ 0) (htop : base 4 = 0) :
    ∃ duration padding, formula+2 ≤ duration ∧
      graphSystem.Block (cfgHalf 216 base move formula 0 0 reserve) duration
        (cfgBudget 366 (bankSelect base (move-1) 0 0 0 (M236Game.child formula move))
          (base 3) (Cantor.pair (move-1) (base 5)) 0 0 (reserve ++ List.replicate padding 0)) [] := by
  exact signed_nonatomic_step 216 366 formula_scan_rows_216 formula_branch_row_216
    child_rows_225 pair_env_rows_237 child_next_225 formula move base reserve htag htop

/-- The positive-phase occurrence already checked in `M236ChildSelect` is an
instance of the same schema. -/
theorem signed_nonatomic_393 (formula move : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (htag : (Cantor.unpair formula).1 ≠ 0) (htop : base 4 = 0) :
    ∃ duration padding, formula+2 ≤ duration ∧
      graphSystem.Block (cfgHalf 393 base move formula 0 0 reserve) duration
        (cfgBudget 546 (bankSelect base (move-1) 0 0 0 (M236Game.child formula move))
          (base 3) (Cantor.pair (move-1) (base 5)) 0 0 (reserve ++ List.replicate padding 0)) [] := by
  exact signed_nonatomic_step 393 546 formula_scan_rows_393 formula_branch_row_393
    child_rows_402 pair_env_rows_414 child_next_402 formula move base reserve htag htop

/-- Second checked negative-phase occurrence, whose continuation is row 723. -/
theorem signed_nonatomic_573 (formula move : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (htag : (Cantor.unpair formula).1 ≠ 0) (htop : base 4 = 0) :
    ∃ duration padding, formula+2 ≤ duration ∧
      graphSystem.Block (cfgHalf 573 base move formula 0 0 reserve) duration
        (cfgBudget 723 (bankSelect base (move-1) 0 0 0 (M236Game.child formula move))
          (base 3) (Cantor.pair (move-1) (base 5)) 0 0 (reserve ++ List.replicate padding 0)) [] := by
  exact signed_nonatomic_step 573 723 formula_scan_rows_573 formula_branch_row_573
    child_rows_582 pair_env_rows_594 child_next_582 formula move base reserve htag htop

/-- Physical lift of the common prepared non-atomic step. -/
theorem selected_signed_nonatomic_step (i k dest : Nat) (scan : FormulaScanRows k) (branch : FormulaBranchRow k)
    (select : ChildSelectRows (k+9)) (pairRows : PairEnvRows (k+9+12)) (next : ChildNextRow (k+9) dest)
    (formula move : Nat) (base : RegisterMachine.Bank 9) (reserve : List Nat)
    (htag : (Cantor.unpair formula).1 ≠ 0) (htop : base 4 = 0)
    (h : graphSystem.run i = cfgHalf k base move formula 0 0 reserve) :
    ∃ duration padding finish, formula+2 ≤ duration ∧ Good finish ∧
      finish.graphState = cfgBudget dest (bankSelect base (move-1) 0 0 0 (M236Game.child formula move))
        (base 3) (Cantor.pair (move-1) (base 5)) 0 0 (reserve ++ List.replicate padding 0) ∧
      graphSystem.run (i+duration) = cfgBudget dest (bankSelect base (move-1) 0 0 0 (M236Game.child formula move))
        (base 3) (Cantor.pair (move-1) (base 5)) 0 0 (reserve ++ List.replicate padding 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run (graphRefinement.boundary (i+duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i+duration) := by
  obtain ⟨duration, padding, ht, block⟩ := signed_nonatomic_step k dest scan branch select pairRows next
    formula move base reserve htag htop
  have hr : graphSystem.run (i+duration) = cfgBudget dest (bankSelect base (move-1) 0 0 0 (M236Game.child formula move))
      (base 3) (Cantor.pair (move-1) (base 5)) 0 0 (reserve ++ List.replicate padding 0) := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i+duration) = graphSystem.prefixWord i := by
    rw [WordEventSystem.prefix_add, h, block.output, List.append_nil]
  obtain ⟨finish, hg, hstate, hconfig⟩ := graphRefinement.related (i+duration)
  refine ⟨duration, padding, finish, ht, hg, hstate.trans hr, hr, hconfig, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

theorem signed_dispatch_rows_192 : CounterDispatchRows 192 := by constructor <;> decide
theorem signed_dispatch_rows_549 : CounterDispatchRows 549 := by constructor <;> decide
theorem signed_unpair_rows_197 : UnpairRows 197 := by constructor <;> decide
theorem signed_unpair_rows_554 : UnpairRows 554 := by constructor <;> decide
theorem signed_emit_rows_208 : EmitRows 208 := by constructor <;> decide
theorem signed_emit_rows_565 : EmitRows 565 := by constructor <;> decide

def signedCoordinateBank (base : RegisterMachine.Bank 9) (count : Nat) : RegisterMachine.Bank 9 :=
  bankAC (bankRest (bankCountTop base count 0) (Cantor.unpair (base 2)).2) (Cantor.unpair (base 2)).1 0

def signedCoordinateReserve (base : RegisterMachine.Bank 9) (reserve : List Nat) (padding : Nat) : List Nat :=
  let q := (Cantor.unpair (base 2)).1
  (((reserve ++ [0]) ++ List.replicate padding 0) ++ List.replicate q 0) ++ List.replicate q 0

/-- The coordinate emission endpoint is a prepared formula scan, with its b
register equal to the unmodified old b. -/
theorem signed_coordinate_to_formula (k : Nat) (base : RegisterMachine.Bank 9) (count : Nat)
    (reserve : List Nat) (padding : Nat) :
    positiveCoordinateExit k base count 0 reserve padding =
      cfgHalf (k+24) (signedCoordinateBank base count) (Cantor.unpair (base 2)).1 (base 7) 0 0
        (signedCoordinateReserve base reserve padding) := by
  unfold positiveCoordinateExit signedCoordinateBank signedCoordinateReserve cfgAS cfgHalf
  simp only [Nat.add_assoc]
  congr 1
  funext i
  fin_cases i <;> simp [bankAS, bankHalf, bankAC, bankRest, bankCountTop]

/-- A positive counter emits one coordinate and performs the corresponding
non-atomic graph update. The output is exactly that coordinate's unary word. -/
theorem signed_coordinate_nonatomic_step (k dest : Nat) (dr : CounterDispatchRows k)
    (ur : UnpairRows (k+5)) (er : EmitRows (k+5+11))
    (scan : FormulaScanRows (k+24)) (branch : FormulaBranchRow (k+24))
    (select : ChildSelectRows (k+24+9)) (pairRows : PairEnvRows (k+24+9+12))
    (next : ChildNextRow (k+24+9) dest)
    (base : RegisterMachine.Bank 9) (count : Nat) (reserve : List Nat)
    (hs : base 0 = 0) (ha : base 6 = 0) (hc : base 8 = 0)
    (htag : (Cantor.unpair (base 7)).1 ≠ 0) :
    ∃ coordDuration coordPadding evalDuration evalPadding,
      base 2+1 ≤ coordDuration ∧ base 7+2 ≤ evalDuration ∧
      graphSystem.Block (cfgCountTop k base (count+1) 0 reserve)
        ((2+(coordDuration+(7*(Cantor.unpair (base 2)).1+3)))+evalDuration)
        (cfgBudget dest
          (bankSelect (signedCoordinateBank base count) ((Cantor.unpair (base 2)).1-1) 0 0 0
            (M236Game.child (base 7) (Cantor.unpair (base 2)).1))
          count (Cantor.pair ((Cantor.unpair (base 2)).1-1) (base 5)) 0 0
          (signedCoordinateReserve base reserve coordPadding ++ List.replicate evalPadding 0))
        (PASoundness.UnaryCodec.unary (Cantor.unpair (base 2)).1) := by
  obtain ⟨d1, p1, hd1, h1⟩ := positive_dispatch_coordinate k dr ur er base count 0 reserve hs ha hc
  rw [signed_coordinate_to_formula k base count reserve p1] at h1
  have htop : signedCoordinateBank base count 4 = 0 := by
    simp [signedCoordinateBank, bankAC, bankRest, bankCountTop]
  obtain ⟨d2, p2, hd2, h2⟩ := signed_nonatomic_step (k+24) dest scan branch select pairRows next
    (base 7) (Cantor.unpair (base 2)).1 (signedCoordinateBank base count)
    (signedCoordinateReserve base reserve p1) htag htop
  have h := h1.trans graphSystem h2
  refine ⟨d1, p1, d2, p2, hd1, hd2, ?_⟩
  simpa [signedCoordinateBank, bankAC, bankRest, bankCountTop] using h

/-- Concrete checked coordinate-and-non-atomic occurrence at row 192. -/
theorem signed_coordinate_nonatomic_192 (base : RegisterMachine.Bank 9) (count : Nat) (reserve : List Nat)
    (hs : base 0 = 0) (ha : base 6 = 0) (hc : base 8 = 0)
    (htag : (Cantor.unpair (base 7)).1 ≠ 0) :
    ∃ coordDuration coordPadding evalDuration evalPadding,
      base 2+1 ≤ coordDuration ∧ base 7+2 ≤ evalDuration ∧
      graphSystem.Block (cfgCountTop 192 base (count+1) 0 reserve)
        ((2+(coordDuration+(7*(Cantor.unpair (base 2)).1+3)))+evalDuration)
        (cfgBudget 366
          (bankSelect (signedCoordinateBank base count) ((Cantor.unpair (base 2)).1-1) 0 0 0
            (M236Game.child (base 7) (Cantor.unpair (base 2)).1))
          count (Cantor.pair ((Cantor.unpair (base 2)).1-1) (base 5)) 0 0
          (signedCoordinateReserve base reserve coordPadding ++ List.replicate evalPadding 0))
        (PASoundness.UnaryCodec.unary (Cantor.unpair (base 2)).1) := by
  exact signed_coordinate_nonatomic_step 192 366 signed_dispatch_rows_192 signed_unpair_rows_197 signed_emit_rows_208
    formula_scan_rows_216 formula_branch_row_216 child_rows_225 pair_env_rows_237 child_next_225
    base count reserve hs ha hc htag

/-- Concrete checked coordinate-and-non-atomic occurrence at row 369. -/
theorem signed_coordinate_nonatomic_369 (base : RegisterMachine.Bank 9) (count : Nat) (reserve : List Nat)
    (hs : base 0 = 0) (ha : base 6 = 0) (hc : base 8 = 0)
    (htag : (Cantor.unpair (base 7)).1 ≠ 0) :
    ∃ coordDuration coordPadding evalDuration evalPadding,
      base 2+1 ≤ coordDuration ∧ base 7+2 ≤ evalDuration ∧
      graphSystem.Block (cfgCountTop 369 base (count+1) 0 reserve)
        ((2+(coordDuration+(7*(Cantor.unpair (base 2)).1+3)))+evalDuration)
        (cfgBudget 546
          (bankSelect (signedCoordinateBank base count) ((Cantor.unpair (base 2)).1-1) 0 0 0
            (M236Game.child (base 7) (Cantor.unpair (base 2)).1))
          count (Cantor.pair ((Cantor.unpair (base 2)).1-1) (base 5)) 0 0
          (signedCoordinateReserve base reserve coordPadding ++ List.replicate evalPadding 0))
        (PASoundness.UnaryCodec.unary (Cantor.unpair (base 2)).1) := by
  exact signed_coordinate_nonatomic_step 369 546 timeout_rows_369 positive_unpair_rows_374 positive_emit_rows_385
    formula_scan_rows_393 formula_branch_row_393 child_rows_402 pair_env_rows_414 child_next_402
    base count reserve hs ha hc htag

/-- Concrete checked coordinate-and-non-atomic occurrence at row 549. -/
theorem signed_coordinate_nonatomic_549 (base : RegisterMachine.Bank 9) (count : Nat) (reserve : List Nat)
    (hs : base 0 = 0) (ha : base 6 = 0) (hc : base 8 = 0)
    (htag : (Cantor.unpair (base 7)).1 ≠ 0) :
    ∃ coordDuration coordPadding evalDuration evalPadding,
      base 2+1 ≤ coordDuration ∧ base 7+2 ≤ evalDuration ∧
      graphSystem.Block (cfgCountTop 549 base (count+1) 0 reserve)
        ((2+(coordDuration+(7*(Cantor.unpair (base 2)).1+3)))+evalDuration)
        (cfgBudget 723
          (bankSelect (signedCoordinateBank base count) ((Cantor.unpair (base 2)).1-1) 0 0 0
            (M236Game.child (base 7) (Cantor.unpair (base 2)).1))
          count (Cantor.pair ((Cantor.unpair (base 2)).1-1) (base 5)) 0 0
          (signedCoordinateReserve base reserve coordPadding ++ List.replicate evalPadding 0))
        (PASoundness.UnaryCodec.unary (Cantor.unpair (base 2)).1) := by
  exact signed_coordinate_nonatomic_step 549 723 signed_dispatch_rows_549 signed_unpair_rows_554 signed_emit_rows_565
    formula_scan_rows_573 formula_branch_row_573 child_rows_582 pair_env_rows_594 child_next_582
    base count reserve hs ha hc htag

def signedCoordinateNonatomicTime (base : RegisterMachine.Bank 9) (coordDuration evalDuration : Nat) : Nat :=
  (2+(coordDuration+(7*(Cantor.unpair (base 2)).1+3)))+evalDuration

def signedCoordinateNonatomicExit (dest : Nat) (base : RegisterMachine.Bank 9) (count : Nat)
    (reserve : List Nat) (coordPadding evalPadding : Nat) : GraphState :=
  cfgBudget dest
    (bankSelect (signedCoordinateBank base count) ((Cantor.unpair (base 2)).1-1) 0 0 0
      (M236Game.child (base 7) (Cantor.unpair (base 2)).1))
    count (Cantor.pair ((Cantor.unpair (base 2)).1-1) (base 5)) 0 0
    (signedCoordinateReserve base reserve coordPadding ++ List.replicate evalPadding 0)

/-- The abstract encoded evaluator uses exactly the child and environment
values established by the local graph step on a nonzero tag. -/
theorem encoded_nonatomic_clause (formula env move : Nat) (negative : Bool) (moves : List Nat)
    (htag : (Cantor.unpair formula).1 ≠ 0) :
    M236Game.encodedPath formula env negative (move :: moves) =
      M236Game.encodedPath (M236Game.child formula move) (Cantor.pair (move-1) env) (!negative) moves := by
  simp [M236Game.encodedPath, M236Game.tag, htag]

/-- Exact named-register projection of a coordinate/non-atomic endpoint. -/
theorem signed_coordinate_nonatomic_registers (dest : Nat) (base : RegisterMachine.Bank 9)
    (count : Nat) (reserve : List Nat) (coordPadding evalPadding : Nat) :
    let s := signedCoordinateNonatomicExit dest base count reserve coordPadding evalPadding
    s.index = dest ∧ s.registers 0 = 0 ∧ s.registers 1 = base 1 ∧
    s.registers 2 = (Cantor.unpair (base 2)).2 ∧ s.registers 3 = count ∧
    s.registers 4 = M236Game.child (base 7) (Cantor.unpair (base 2)).1 ∧
    s.registers 5 = Cantor.pair ((Cantor.unpair (base 2)).1-1) (base 5) ∧
    s.registers 6 = 0 ∧ s.registers 7 = 0 ∧ s.registers 8 = 0 := by
  simp [signedCoordinateNonatomicExit, signedCoordinateBank, cfgBudget, bankSelect,
    bankHalf, bankAC, bankRest, bankCountTop, bankBudget, RegisterMachine.write]

/-- Physical lift of a coordinate-emission and non-atomic update, conditional
on reaching its prepared positive-count entry on the selected run. -/
theorem selected_signed_coordinate_nonatomic_step (i k dest : Nat) (dr : CounterDispatchRows k)
    (ur : UnpairRows (k+5)) (er : EmitRows (k+5+11))
    (scan : FormulaScanRows (k+24)) (branch : FormulaBranchRow (k+24))
    (select : ChildSelectRows (k+24+9)) (pairRows : PairEnvRows (k+24+9+12))
    (next : ChildNextRow (k+24+9) dest)
    (base : RegisterMachine.Bank 9) (count : Nat) (reserve : List Nat)
    (hs : base 0 = 0) (ha : base 6 = 0) (hc : base 8 = 0)
    (htag : (Cantor.unpair (base 7)).1 ≠ 0)
    (h : graphSystem.run i = cfgCountTop k base (count+1) 0 reserve) :
    ∃ coordDuration coordPadding evalDuration evalPadding finish,
      base 2+1 ≤ coordDuration ∧ base 7+2 ≤ evalDuration ∧ Good finish ∧
      finish.graphState = signedCoordinateNonatomicExit dest base count reserve coordPadding evalPadding ∧
      graphSystem.run (i+signedCoordinateNonatomicTime base coordDuration evalDuration) =
        signedCoordinateNonatomicExit dest base count reserve coordPadding evalPadding ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i+signedCoordinateNonatomicTime base coordDuration evalDuration)) ∧
      (machineWordSystem machine machineLabels).prefixWord
          (graphRefinement.boundary (i+signedCoordinateNonatomicTime base coordDuration evalDuration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++
          PASoundness.UnaryCodec.unary (Cantor.unpair (base 2)).1 ∧
      graphRefinement.boundary i < graphRefinement.boundary (i+signedCoordinateNonatomicTime base coordDuration evalDuration) := by
  obtain ⟨d1, p1, d2, p2, hd1, hd2, block⟩ :=
    signed_coordinate_nonatomic_step k dest dr ur er scan branch select pairRows next base count reserve hs ha hc htag
  change graphSystem.Block (cfgCountTop k base (count+1) 0 reserve) (signedCoordinateNonatomicTime base d1 d2)
    (signedCoordinateNonatomicExit dest base count reserve p1 p2) _ at block
  have hr : graphSystem.run (i+signedCoordinateNonatomicTime base d1 d2) =
      signedCoordinateNonatomicExit dest base count reserve p1 p2 := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i+signedCoordinateNonatomicTime base d1 d2) =
      graphSystem.prefixWord i ++ PASoundness.UnaryCodec.unary (Cantor.unpair (base 2)).1 := by
    rw [WordEventSystem.prefix_add, h, block.output]
  obtain ⟨finish, hg, hstate, hconfig⟩ := graphRefinement.related (i+signedCoordinateNonatomicTime base d1 d2)
  refine ⟨d1, p1, d2, p2, finish, hd1, hd2, hg, hstate.trans hr, hr, hconfig, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    simp only [signedCoordinateNonatomicTime]
    omega

end PASoundness.M236.OccurrenceGraph
