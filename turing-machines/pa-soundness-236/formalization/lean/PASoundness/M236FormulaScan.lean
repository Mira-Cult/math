import PASoundness.M236PositiveCoordinate

/-! Register-renamed Cantor scan and tag branch in the retained occurrence graph.
The pinned producer's `CantorTagged.signed_step` uses `unpair(c,scratch,b)`;
this file verifies the literal graph only, not Python producer correspondence. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

/-- The input is b, the diagonal coordinate is c, and the auxiliary is scratch. -/
structure FormulaScanRows (k : Nat) : Prop where
  restDec : sourceRows[k]? = some ("3.k.b.decnz", k+1, some (k+8))
  cInc : sourceRows[k+1]? = some ("3.scratch.copy.inc", k+2, none)
  aDec : sourceRows[k+2]? = some ("3.k.c.decnz", k+3, some (k+4))
  jump3 : sourceRows[k+3]? = some ("jump", k+7, none)
  cDec : sourceRows[k+4]? = some ("3.scratch.copy.decnz", k+5, some (k+7))
  aInc : sourceRows[k+5]? = some ("3.k.c.inc", k+6, none)
  jump6 : sourceRows[k+6]? = some ("jump", k+4, none)
  jump7 : sourceRows[k+7]? = some ("jump", k, none)

structure FormulaBranchRow (k : Nat) : Prop where
  branch : sourceRows[k+8]? = some ("3.k.c.decnz", k+9, some (k+35))

theorem formula_scan_rows_216 : FormulaScanRows 216 := by constructor <;> decide
theorem formula_scan_rows_393 : FormulaScanRows 393 := by constructor <;> decide
theorem formula_scan_rows_573 : FormulaScanRows 573 := by constructor <;> decide
theorem formula_branch_row_216 : FormulaBranchRow 216 := ⟨by decide⟩
theorem formula_branch_row_393 : FormulaBranchRow 393 := ⟨by decide⟩
theorem formula_branch_row_573 : FormulaBranchRow 573 := ⟨by decide⟩

theorem formula_dec_input (focus : Nat) (k : Nat) (rows : FormulaScanRows k)
    (base : RegisterMachine.Bank 9) (n a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf k base focus (n+1) a c reserve) =
      (cfgHalf (k+1) base focus n a c (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.restDec, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])


theorem formula_zero_input (focus : Nat) (k : Nat) (rows : FormulaScanRows k)
    (base : RegisterMachine.Bank 9) (a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf k base focus 0 a c reserve) = (cfgHalf (k+8) base focus 0 a c reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.restDec, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]



theorem formula_inc_aux (focus : Nat) (k : Nat) (rows : FormulaScanRows k)
    (base : RegisterMachine.Bank 9) (rest a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+1) base focus rest a c reserve) =
      (cfgHalf (k+2) base focus rest a (c+1) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.cInc, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])


theorem formula_dec_diagonal (focus : Nat) (k : Nat) (rows : FormulaScanRows k)
    (base : RegisterMachine.Bank 9) (rest n c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+2) base focus rest (n+1) c reserve) =
      (cfgHalf (k+3) base focus rest n c (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.aDec, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])


theorem formula_zero_diagonal (focus : Nat) (k : Nat) (rows : FormulaScanRows k)
    (base : RegisterMachine.Bank 9) (rest c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+2) base focus rest 0 c reserve) =
      (cfgHalf (k+4) base focus rest 0 c reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.aDec, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]


theorem formula_jump3 (focus : Nat) (k : Nat) (rows : FormulaScanRows k)
    (base : RegisterMachine.Bank 9) (rest a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+3) base focus rest a c reserve) =
      (cfgHalf (k+7) base focus rest a c reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.jump3, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]


theorem formula_dec_aux (focus : Nat) (k : Nat) (rows : FormulaScanRows k)
    (base : RegisterMachine.Bank 9) (rest a n : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+4) base focus rest a (n+1) reserve) =
      (cfgHalf (k+5) base focus rest a n (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.cDec, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])


theorem formula_zero_aux (focus : Nat) (k : Nat) (rows : FormulaScanRows k)
    (base : RegisterMachine.Bank 9) (rest a : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+4) base focus rest a 0 reserve) =
      (cfgHalf (k+7) base focus rest a 0 reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.cDec, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]


theorem formula_inc_diagonal (focus : Nat) (k : Nat) (rows : FormulaScanRows k)
    (base : RegisterMachine.Bank 9) (rest a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+5) base focus rest a c reserve) =
      (cfgHalf (k+6) base focus rest (a+1) c reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.aInc, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])


theorem formula_jump6 (focus : Nat) (k : Nat) (rows : FormulaScanRows k)
    (base : RegisterMachine.Bank 9) (rest a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+6) base focus rest a c reserve) =
      (cfgHalf (k+4) base focus rest a c reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.jump6, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]


theorem formula_jump7 (focus : Nat) (k : Nat) (rows : FormulaScanRows k)
    (base : RegisterMachine.Bank 9) (rest a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+7) base focus rest a c reserve) =
      (cfgHalf (k) base focus rest a c reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.jump7, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]


theorem formula_move_cycle (focus : Nat) (k : Nat) (rows : FormulaScanRows k) (base : RegisterMachine.Bank 9)
    (rest a n : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf (k+4) base focus rest a (n+1) reserve) 3
      (cfgHalf (k+4) base focus rest (a+1) n (reserve ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (formula_dec_aux focus k rows base rest a n reserve)
  have h2 := WordEventSystem.Block.single graphSystem (formula_inc_diagonal focus k rows base rest a n (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (formula_jump6 focus k rows base rest (a+1) n (reserve ++ [0]))
  simpa using (h1.trans graphSystem h2).trans graphSystem h3


theorem formula_move_all (focus : Nat) (n k : Nat) (rows : FormulaScanRows k) (base : RegisterMachine.Bank 9)
    (rest a : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf (k+4) base focus rest a n reserve) (3*n)
      (cfgHalf (k+4) base focus rest (a+n) 0 (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing a reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgHalf (k+4) base focus rest a 0 reserve)
  | succ n ih =>
    have h := (formula_move_cycle focus k rows base rest a n reserve).trans graphSystem (ih (a+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h


theorem formula_move_aux_to_diagonal (focus : Nat) (n k : Nat) (rows : FormulaScanRows k) (base : RegisterMachine.Bank 9)
    (rest a : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf (k+4) base focus rest a n reserve) (3*n+2)
      (cfgHalf k base focus rest (a+n) 0 (reserve ++ List.replicate n 0)) [] := by
  have h1 := formula_move_all focus n k rows base rest a reserve
  have h2 := WordEventSystem.Block.single graphSystem (formula_zero_aux focus k rows base rest (a+n) (reserve ++ List.replicate n 0))
  have h3 := WordEventSystem.Block.single graphSystem (formula_jump7 focus k rows base rest (a+n) 0 (reserve ++ List.replicate n 0))
  simpa [Nat.add_assoc] using (h1.trans graphSystem h2).trans graphSystem h3


theorem formula_diagonal_positive (focus : Nat) (k : Nat) (rows : FormulaScanRows k) (base : RegisterMachine.Bank 9)
    (rest a c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf k base focus (rest+1) (a+1) c reserve) 5
      (cfgHalf k base focus rest a (c+1) ((reserve ++ [0]) ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (formula_dec_input focus k rows base rest (a+1) c reserve)
  have h2 := WordEventSystem.Block.single graphSystem (formula_inc_aux focus k rows base rest (a+1) c (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (formula_dec_diagonal focus k rows base rest a (c+1) (reserve ++ [0]))
  have h4 := WordEventSystem.Block.single graphSystem (formula_jump3 focus k rows base rest a (c+1) ((reserve ++ [0]) ++ [0]))
  have h5 := WordEventSystem.Block.single graphSystem (formula_jump7 focus k rows base rest a (c+1) ((reserve ++ [0]) ++ [0]))
  simpa using ((((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4).trans graphSystem h5)


theorem formula_diagonal_zero (focus : Nat) (k : Nat) (rows : FormulaScanRows k) (base : RegisterMachine.Bank 9)
    (rest c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf k base focus (rest+1) 0 c reserve) (3*(c+1)+5)
      (cfgHalf k base focus rest (c+1) 0 ((reserve ++ [0]) ++ List.replicate (c+1) 0)) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (formula_dec_input focus k rows base rest 0 c reserve)
  have h2 := WordEventSystem.Block.single graphSystem (formula_inc_aux focus k rows base rest 0 c (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (formula_zero_diagonal focus k rows base rest (c+1) (reserve ++ [0]))
  have h4 := formula_move_aux_to_diagonal focus (c+1) k rows base rest 0 (reserve ++ [0])
  have h := ((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4
  have ht : 3 + (3*(c+1)+2) = 3*(c+1)+5 := by omega
  simpa only [Nat.zero_add, List.nil_append, Nat.reduceAdd, ht] using h


theorem formula_diagonal_phase (focus : Nat) (remaining k : Nat) (rows : FormulaScanRows k) (base : RegisterMachine.Bank 9)
    (a c : Nat) (reserve : List Nat) :
    ∃ duration padding, remaining+1 ≤ duration ∧
      graphSystem.Block (cfgHalf k base focus remaining a c reserve) duration
        (cfgHalf (k+8) base focus 0 (M236.UnpairDiagonal.walk remaining (a,c)).1
          (M236.UnpairDiagonal.walk remaining (a,c)).2
          (reserve ++ List.replicate padding 0)) [] := by
  induction remaining generalizing a c reserve with
  | zero =>
    refine ⟨1, 0, by omega, ?_⟩
    simpa [M236.UnpairDiagonal.walk] using WordEventSystem.Block.single graphSystem (formula_zero_input focus k rows base a c reserve)
  | succ n ih =>
    cases a with
    | zero =>
      obtain ⟨duration, padding, ht, htail⟩ := ih (c+1) 0 ((reserve ++ [0]) ++ List.replicate (c+1) 0)
      have h := (formula_diagonal_zero focus k rows base n c reserve).trans graphSystem htail
      refine ⟨3*(c+1)+5+duration, (c+2)+padding, by omega, ?_⟩
      have hres : ((reserve ++ [0]) ++ List.replicate (c+1) 0) ++ List.replicate padding 0 =
          reserve ++ List.replicate ((c+2)+padding) 0 := by
        have hrep : List.replicate (c+2) (0 : Nat) = 0 :: List.replicate (c+1) 0 := rfl
        conv_rhs => rw [List.replicate_add, hrep]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
      rw [← hres]
      simpa only [M236.UnpairDiagonal.walk, M236.UnpairDiagonal.next,
        Prod.fst, Prod.snd, List.nil_append] using h
    | succ a =>
      obtain ⟨duration, padding, ht, htail⟩ := ih a (c+1) ((reserve ++ [0]) ++ [0])
      have h := (formula_diagonal_positive focus k rows base n a c reserve).trans graphSystem htail
      refine ⟨5+duration, 2+padding, by omega, ?_⟩
      have hres : ((reserve ++ [0]) ++ [0]) ++ List.replicate padding 0 =
          reserve ++ List.replicate (2+padding) 0 := by
        conv_rhs => rw [List.replicate_add]
        simp only [List.replicate_succ, List.replicate_zero, List.append_assoc, List.cons_append, List.nil_append]
      rw [← hres]
      simpa only [M236.UnpairDiagonal.walk, M236.UnpairDiagonal.next,
        Prod.fst, Prod.snd, List.nil_append] using h


theorem formula_diagonal_unpair (focus : Nat) (n k : Nat) (rows : FormulaScanRows k) (base : RegisterMachine.Bank 9) (reserve : List Nat) :
    ∃ duration padding, n+1 ≤ duration ∧
      graphSystem.Block (cfgHalf k base focus n 0 0 reserve) duration
        (cfgHalf (k+8) base focus 0 (Cantor.unpair n).1 (Cantor.unpair n).2
          (reserve ++ List.replicate padding 0)) [] := by
  simpa only [M236.UnpairDiagonal.walk_zero] using formula_diagonal_phase focus n k rows base 0 0 reserve




/-- The first Cantor component selects a zero or positive tag branch. -/
theorem formula_branch_zero (focus k : Nat) (rows : FormulaBranchRow k)
    (base : RegisterMachine.Bank 9) (b scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+8) base focus b 0 scratch reserve) =
      (cfgHalf (k+35) base focus b 0 scratch reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.branch, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem formula_branch_positive (focus k : Nat) (rows : FormulaBranchRow k)
    (base : RegisterMachine.Bank 9) (b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+8) base focus b (c+1) scratch reserve) =
      (cfgHalf (k+9) base focus b c scratch (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.branch, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

/-- A zero first component exits through the second target. The final branch
step leaves the scan-exit bank unchanged and emits no bit. -/
theorem formula_unpair_zero_branch (focus n k : Nat) (rows : FormulaScanRows k)
    (branch : FormulaBranchRow k) (base : RegisterMachine.Bank 9) (reserve : List Nat)
    (hzero : (Cantor.unpair n).1 = 0) :
    ∃ duration padding, n+2 ≤ duration ∧
      graphSystem.Block (cfgHalf k base focus n 0 0 reserve) duration
        (cfgHalf (k+35) base focus 0 0 (Cantor.unpair n).2
          (reserve ++ List.replicate padding 0)) [] := by
  obtain ⟨duration, padding, ht, hscan⟩ := formula_diagonal_unpair focus n k rows base reserve
  rw [hzero] at hscan
  have hbranch := WordEventSystem.Block.single graphSystem
    (formula_branch_zero focus k branch base 0 (Cantor.unpair n).2 (reserve ++ List.replicate padding 0))
  refine ⟨duration+1, padding, by omega, ?_⟩
  simpa using hscan.trans graphSystem hbranch

/-- A positive first component is decremented on the first target; the second
component is preserved in scratch. -/
theorem formula_unpair_positive_branch (focus n k tag : Nat) (rows : FormulaScanRows k)
    (branch : FormulaBranchRow k) (base : RegisterMachine.Bank 9) (reserve : List Nat)
    (hpositive : (Cantor.unpair n).1 = tag+1) :
    ∃ duration padding, n+2 ≤ duration ∧
      graphSystem.Block (cfgHalf k base focus n 0 0 reserve) duration
        (cfgHalf (k+9) base focus 0 tag (Cantor.unpair n).2
          (reserve ++ List.replicate padding 0)) [] := by
  obtain ⟨duration, padding, ht, hscan⟩ := formula_diagonal_unpair focus n k rows base reserve
  rw [hpositive] at hscan
  have hbranch := WordEventSystem.Block.single graphSystem
    (formula_branch_positive focus k branch base 0 tag (Cantor.unpair n).2 (reserve ++ List.replicate padding 0))
  have h := hscan.trans graphSystem hbranch
  refine ⟨duration+1, padding+1, by omega, ?_⟩
  have hr : (reserve ++ List.replicate padding 0) ++ [0] = reserve ++ List.replicate (padding+1) 0 := by
    change (reserve ++ List.replicate padding 0) ++ List.replicate 1 0 = _
    simp only [List.append_assoc, ← List.replicate_add]
  rw [hr] at h
  simpa using h

/-- Physical lift of the arbitrary-input formula scan at an explicitly reached
prepared graph entry. -/
theorem selected_formula_diagonal_unpair (i focus n k : Nat) (rows : FormulaScanRows k)
    (base : RegisterMachine.Bank 9) (reserve : List Nat)
    (h : graphSystem.run i = cfgHalf k base focus n 0 0 reserve) :
    ∃ duration padding finish, n+1 ≤ duration ∧ Good finish ∧
      finish.graphState = cfgHalf (k+8) base focus 0 (Cantor.unpair n).1 (Cantor.unpair n).2
        (reserve ++ List.replicate padding 0) ∧
      graphSystem.run (i+duration) = cfgHalf (k+8) base focus 0 (Cantor.unpair n).1 (Cantor.unpair n).2
        (reserve ++ List.replicate padding 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run (graphRefinement.boundary (i+duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i+duration) := by
  obtain ⟨duration, padding, ht, block⟩ := formula_diagonal_unpair focus n k rows base reserve
  have hr : graphSystem.run (i+duration) = cfgHalf (k+8) base focus 0 (Cantor.unpair n).1 (Cantor.unpair n).2
      (reserve ++ List.replicate padding 0) := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i+duration) = graphSystem.prefixWord i := by
    rw [WordEventSystem.prefix_add, h, block.output, List.append_nil]
  obtain ⟨finish, hg, hstate, hconfig⟩ := graphRefinement.related (i+duration)
  refine ⟨duration, padding, finish, ht, hg, hstate.trans hr, hr, hconfig, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

def positiveOneFormulaBank (base : RegisterMachine.Bank 9) (count top : Nat) : RegisterMachine.Bank 9 :=
  bankAC (bankRest (bankCountTop (timeoutBank base top 0) count 0) (Cantor.unpair (base 2)).2)
    (Cantor.unpair (base 2)).1 0

def positiveOneFormulaReserve (base : RegisterMachine.Bank 9) (top : Nat) (reserve : List Nat) (padding : Nat) : List Nat :=
  let q := (Cantor.unpair (base 2)).1
  (((((reserve ++ [0]) ++ List.replicate top 0) ++ [0]) ++ List.replicate padding 0) ++
    List.replicate q 0) ++ List.replicate q 0

theorem positive_one_to_formula_view (base : RegisterMachine.Bank 9) (count top : Nat)
    (reserve : List Nat) (padding : Nat) :
    positiveCoordinateExit 369 (timeoutBank base top 0) count 0
      ((reserve ++ [0]) ++ List.replicate top 0) padding =
      cfgHalf 393 (positiveOneFormulaBank base count top) (Cantor.unpair (base 2)).1 top 0 0
        (positiveOneFormulaReserve base top reserve padding) := by
  unfold positiveCoordinateExit positiveOneFormulaBank positiveOneFormulaReserve cfgAS cfgHalf
  simp only [show timeoutBank base top 0 2 = base 2 by simp [timeoutBank]]
  congr 1
  funext j
  fin_cases j <;> simp [bankAS, bankHalf, bankAC, bankRest, bankCountTop, timeoutBank]

/-- From the prepared one-bit positive-count state, emit the next coordinate,
then silently decode the saved formula into its Cantor components at row 401. -/
theorem positive_one_coordinate_formula_scan (base : RegisterMachine.Bank 9) (count top : Nat)
    (reserve : List Nat) (hs : base 0 = 0) (hcount : base 3 = count+1)
    (ha : base 6 = 0) (hc : base 8 = 0) :
    ∃ coordDuration coordPadding scanDuration scanPadding,
      base 2+1 ≤ coordDuration ∧ top+1 ≤ scanDuration ∧
      graphSystem.Block (cfgTimeout 161 base 1 top reserve)
        (((3*top+3)+(2+(coordDuration+(7*(Cantor.unpair (base 2)).1+3))))+scanDuration)
        (cfgHalf 401 (positiveOneFormulaBank base count top) (Cantor.unpair (base 2)).1 0
          (Cantor.unpair top).1 (Cantor.unpair top).2
          (positiveOneFormulaReserve base top reserve coordPadding ++ List.replicate scanPadding 0))
        (PASoundness.UnaryCodec.unary (Cantor.unpair (base 2)).1) := by
  obtain ⟨coordDuration, coordPadding, ht, hcoord⟩ := positive_one_to_393 base count top reserve hs hcount ha hc
  rw [positive_one_to_formula_view base count top reserve coordPadding] at hcoord
  obtain ⟨scanDuration, scanPadding, hscan, hformula⟩ :=
    formula_diagonal_unpair (Cantor.unpair (base 2)).1 top 393 formula_scan_rows_393
      (positiveOneFormulaBank base count top) (positiveOneFormulaReserve base top reserve coordPadding)
  refine ⟨coordDuration, coordPadding, scanDuration, scanPadding, ht, hscan, ?_⟩
  simpa using hcoord.trans graphSystem hformula

/-- The one-bit path takes the zero-tag target at row 428, retaining the
payload and the emitted coordinate. -/
theorem positive_one_coordinate_formula_zero (base : RegisterMachine.Bank 9) (count top : Nat)
    (reserve : List Nat) (hs : base 0 = 0) (hcount : base 3 = count+1)
    (ha : base 6 = 0) (hc : base 8 = 0) (hzero : (Cantor.unpair top).1 = 0) :
    ∃ coordDuration coordPadding scanDuration scanPadding,
      base 2+1 ≤ coordDuration ∧ top+1 ≤ scanDuration ∧
      graphSystem.Block (cfgTimeout 161 base 1 top reserve)
        ((((3*top+3)+(2+(coordDuration+(7*(Cantor.unpair (base 2)).1+3))))+scanDuration)+1)
        (cfgHalf 428 (positiveOneFormulaBank base count top) (Cantor.unpair (base 2)).1 0
          0 (Cantor.unpair top).2
          (positiveOneFormulaReserve base top reserve coordPadding ++ List.replicate scanPadding 0))
        (PASoundness.UnaryCodec.unary (Cantor.unpair (base 2)).1) := by
  obtain ⟨d1, p1, d2, p2, ht1, ht2, hscan⟩ := positive_one_coordinate_formula_scan base count top reserve hs hcount ha hc
  rw [hzero] at hscan
  have hbranch := WordEventSystem.Block.single graphSystem
    (formula_branch_zero (Cantor.unpair (base 2)).1 393 formula_branch_row_393
      (positiveOneFormulaBank base count top) 0 (Cantor.unpair top).2
      (positiveOneFormulaReserve base top reserve p1 ++ List.replicate p2 0))
  exact ⟨d1, p1, d2, p2, ht1, ht2, by simpa using hscan.trans graphSystem hbranch⟩

/-- The one-bit path takes the positive-tag target at row 402, consuming one
from that tag while retaining the payload and emitted coordinate. -/
theorem positive_one_coordinate_formula_positive (base : RegisterMachine.Bank 9) (count top tag : Nat)
    (reserve : List Nat) (hs : base 0 = 0) (hcount : base 3 = count+1)
    (ha : base 6 = 0) (hc : base 8 = 0) (hpositive : (Cantor.unpair top).1 = tag+1) :
    ∃ coordDuration coordPadding scanDuration scanPadding,
      base 2+1 ≤ coordDuration ∧ top+1 ≤ scanDuration ∧
      graphSystem.Block (cfgTimeout 161 base 1 top reserve)
        ((((3*top+3)+(2+(coordDuration+(7*(Cantor.unpair (base 2)).1+3))))+scanDuration)+1)
        (cfgHalf 402 (positiveOneFormulaBank base count top) (Cantor.unpair (base 2)).1 0
          tag (Cantor.unpair top).2
          (positiveOneFormulaReserve base top reserve coordPadding ++ List.replicate (scanPadding+1) 0))
        (PASoundness.UnaryCodec.unary (Cantor.unpair (base 2)).1) := by
  obtain ⟨d1, p1, d2, p2, ht1, ht2, hscan⟩ := positive_one_coordinate_formula_scan base count top reserve hs hcount ha hc
  rw [hpositive] at hscan
  have hbranch := WordEventSystem.Block.single graphSystem
    (formula_branch_positive (Cantor.unpair (base 2)).1 393 formula_branch_row_393
      (positiveOneFormulaBank base count top) 0 tag (Cantor.unpair top).2
      (positiveOneFormulaReserve base top reserve p1 ++ List.replicate p2 0))
  have h := hscan.trans graphSystem hbranch
  have hr : (positiveOneFormulaReserve base top reserve p1 ++ List.replicate p2 0) ++ [0] =
      positiveOneFormulaReserve base top reserve p1 ++ List.replicate (p2+1) 0 := by
    change (positiveOneFormulaReserve base top reserve p1 ++ List.replicate p2 0) ++ List.replicate 1 0 = _
    simp only [List.append_assoc, ← List.replicate_add]
  rw [hr] at h
  exact ⟨d1, p1, d2, p2, ht1, ht2, by simpa using h⟩

end PASoundness.M236.OccurrenceGraph
