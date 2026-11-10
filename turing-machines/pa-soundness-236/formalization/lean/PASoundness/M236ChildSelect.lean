import PASoundness.M236FormulaScan
import PASoundness.M236PairEnvironment

/-! Prepared positive-tag child selection and environment update. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

def bankSelect (base : RegisterMachine.Bank 9) (a b c scratch top : Nat) : RegisterMachine.Bank 9 :=
  bankHalf (RegisterMachine.write base 4 top) a b c scratch

def cfgSelect (i : Nat) (base : RegisterMachine.Bank 9) (a b c scratch top : Nat) (reserve : List Nat) : GraphState :=
  ⟨i, bankSelect base a b c scratch top, reserve⟩

structure ChildSelectRows (k : Nat) : Prop where
  row0 : sourceRows[k]? = some ("3.k.a.decnz", k+1, some (k+7))
  row1 : sourceRows[k+1]? = some ("3.k.c.decnz", k+2, some (k+3))
  row2 : sourceRows[k+2]? = some ("jump", k+1, none)
  row3 : sourceRows[k+3]? = some ("3.scratch.copy.decnz", k+4, some (k+6))
  row4 : sourceRows[k+4]? = some ("3.k.c.inc", k+5, none)
  row5 : sourceRows[k+5]? = some ("jump", k+3, none)
  row6 : sourceRows[k+6]? = some ("jump", k+9, none)
  row7 : sourceRows[k+7]? = some ("3.scratch.copy.decnz", k+8, some (k+9))
  row8 : sourceRows[k+8]? = some ("jump", k+7, none)
  row9 : sourceRows[k+9]? = some ("3.k.c.decnz", k+10, some (k+12))
  row10 : sourceRows[k+10]? = some ("3.k.top.inc", k+11, none)
  row11 : sourceRows[k+11]? = some ("jump", k+9, none)

theorem child_rows_225 : ChildSelectRows 225 := by constructor <;> decide
theorem child_rows_402 : ChildSelectRows 402 := by constructor <;> decide
theorem child_rows_582 : ChildSelectRows 582 := by constructor <;> decide

theorem child_dec_a (k : Nat) (rows : ChildSelectRows k) (base : RegisterMachine.Bank 9)
    (a b c scratch top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgSelect k base (a+1) (b) (c) (scratch) (top) reserve) =
      (cfgSelect (k+1) base (a) (b) (c) (scratch) (top) (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgSelect, rows.row0, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankSelect, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem child_zero_a (k : Nat) (rows : ChildSelectRows k) (base : RegisterMachine.Bank 9)
    (_a b c scratch top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgSelect k base (0) (b) (c) (scratch) (top) reserve) =
      (cfgSelect (k+7) base (0) (b) (c) (scratch) (top) reserve, []) := by
  simp [graphSystem, graphNext, cfgSelect, rows.row0, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankSelect, bankHalf, RegisterMachine.execute]

theorem child_dec_c_clear (k : Nat) (rows : ChildSelectRows k) (base : RegisterMachine.Bank 9)
    (a b c scratch top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgSelect (k+1) base (a) (b) (c+1) (scratch) (top) reserve) =
      (cfgSelect (k+2) base (a) (b) (c) (scratch) (top) (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgSelect, rows.row1, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankSelect, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem child_zero_c_clear (k : Nat) (rows : ChildSelectRows k) (base : RegisterMachine.Bank 9)
    (a b _c scratch top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgSelect (k+1) base (a) (b) (0) (scratch) (top) reserve) =
      (cfgSelect (k+3) base (a) (b) (0) (scratch) (top) reserve, []) := by
  simp [graphSystem, graphNext, cfgSelect, rows.row1, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankSelect, bankHalf, RegisterMachine.execute]

theorem child_jump2 (k : Nat) (rows : ChildSelectRows k) (base : RegisterMachine.Bank 9)
    (a b c scratch top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgSelect (k+2) base (a) (b) (c) (scratch) (top) reserve) =
      (cfgSelect (k+1) base (a) (b) (c) (scratch) (top) reserve, []) := by
  simp [graphSystem, graphNext, cfgSelect, rows.row2, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankSelect, bankHalf, RegisterMachine.execute]

theorem child_dec_s_move (k : Nat) (rows : ChildSelectRows k) (base : RegisterMachine.Bank 9)
    (a b c scratch top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgSelect (k+3) base (a) (b) (c) (scratch+1) (top) reserve) =
      (cfgSelect (k+4) base (a) (b) (c) (scratch) (top) (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgSelect, rows.row3, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankSelect, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem child_zero_s_move (k : Nat) (rows : ChildSelectRows k) (base : RegisterMachine.Bank 9)
    (a b c _scratch top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgSelect (k+3) base (a) (b) (c) (0) (top) reserve) =
      (cfgSelect (k+6) base (a) (b) (c) (0) (top) reserve, []) := by
  simp [graphSystem, graphNext, cfgSelect, rows.row3, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankSelect, bankHalf, RegisterMachine.execute]

theorem child_inc_c (k : Nat) (rows : ChildSelectRows k) (base : RegisterMachine.Bank 9)
    (a b c scratch top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgSelect (k+4) base (a) (b) (c) (scratch) (top) reserve) =
      (cfgSelect (k+5) base (a) (b) (c+1) (scratch) (top) reserve, []) := by
  simp [graphSystem, graphNext, cfgSelect, rows.row4, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankSelect, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem child_jump5 (k : Nat) (rows : ChildSelectRows k) (base : RegisterMachine.Bank 9)
    (a b c scratch top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgSelect (k+5) base (a) (b) (c) (scratch) (top) reserve) =
      (cfgSelect (k+3) base (a) (b) (c) (scratch) (top) reserve, []) := by
  simp [graphSystem, graphNext, cfgSelect, rows.row5, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankSelect, bankHalf, RegisterMachine.execute]

theorem child_jump6 (k : Nat) (rows : ChildSelectRows k) (base : RegisterMachine.Bank 9)
    (a b c scratch top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgSelect (k+6) base (a) (b) (c) (scratch) (top) reserve) =
      (cfgSelect (k+9) base (a) (b) (c) (scratch) (top) reserve, []) := by
  simp [graphSystem, graphNext, cfgSelect, rows.row6, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankSelect, bankHalf, RegisterMachine.execute]

theorem child_dec_s_clear (k : Nat) (rows : ChildSelectRows k) (base : RegisterMachine.Bank 9)
    (a b c scratch top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgSelect (k+7) base (a) (b) (c) (scratch+1) (top) reserve) =
      (cfgSelect (k+8) base (a) (b) (c) (scratch) (top) (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgSelect, rows.row7, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankSelect, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem child_zero_s_clear (k : Nat) (rows : ChildSelectRows k) (base : RegisterMachine.Bank 9)
    (a b c _scratch top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgSelect (k+7) base (a) (b) (c) (0) (top) reserve) =
      (cfgSelect (k+9) base (a) (b) (c) (0) (top) reserve, []) := by
  simp [graphSystem, graphNext, cfgSelect, rows.row7, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankSelect, bankHalf, RegisterMachine.execute]

theorem child_jump8 (k : Nat) (rows : ChildSelectRows k) (base : RegisterMachine.Bank 9)
    (a b c scratch top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgSelect (k+8) base (a) (b) (c) (scratch) (top) reserve) =
      (cfgSelect (k+7) base (a) (b) (c) (scratch) (top) reserve, []) := by
  simp [graphSystem, graphNext, cfgSelect, rows.row8, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankSelect, bankHalf, RegisterMachine.execute]

theorem child_dec_c_top (k : Nat) (rows : ChildSelectRows k) (base : RegisterMachine.Bank 9)
    (a b c scratch top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgSelect (k+9) base (a) (b) (c+1) (scratch) (top) reserve) =
      (cfgSelect (k+10) base (a) (b) (c) (scratch) (top) (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgSelect, rows.row9, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankSelect, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem child_zero_c_top (k : Nat) (rows : ChildSelectRows k) (base : RegisterMachine.Bank 9)
    (a b _c scratch top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgSelect (k+9) base (a) (b) (0) (scratch) (top) reserve) =
      (cfgSelect (k+12) base (a) (b) (0) (scratch) (top) reserve, []) := by
  simp [graphSystem, graphNext, cfgSelect, rows.row9, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankSelect, bankHalf, RegisterMachine.execute]

theorem child_inc_top (k : Nat) (rows : ChildSelectRows k) (base : RegisterMachine.Bank 9)
    (a b c scratch top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgSelect (k+10) base (a) (b) (c) (scratch) (top) reserve) =
      (cfgSelect (k+11) base (a) (b) (c) (scratch) (top+1) reserve, []) := by
  simp [graphSystem, graphNext, cfgSelect, rows.row10, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankSelect, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem child_jump11 (k : Nat) (rows : ChildSelectRows k) (base : RegisterMachine.Bank 9)
    (a b c scratch top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgSelect (k+11) base (a) (b) (c) (scratch) (top) reserve) =
      (cfgSelect (k+9) base (a) (b) (c) (scratch) (top) reserve, []) := by
  simp [graphSystem, graphNext, cfgSelect, rows.row11, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankSelect, bankHalf, RegisterMachine.execute]

theorem child_clear_c (n k : Nat) (rows : ChildSelectRows k) (base : RegisterMachine.Bank 9)
    (a b scratch top : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgSelect (k+1) base a b n scratch top reserve) (2*n+1)
      (cfgSelect (k+3) base a b 0 scratch top (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing reserve with
  | zero => simpa using WordEventSystem.Block.single graphSystem (child_zero_c_clear k rows base a b 0 scratch top reserve)
  | succ n ih =>
    have h1 := WordEventSystem.Block.single graphSystem (child_dec_c_clear k rows base a b n scratch top reserve)
    have h2 := WordEventSystem.Block.single graphSystem (child_jump2 k rows base a b n scratch top (reserve ++ [0]))
    have h := (h1.trans graphSystem h2).trans graphSystem (ih (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem child_move_scratch (n k : Nat) (rows : ChildSelectRows k) (base : RegisterMachine.Bank 9)
    (a b c top : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgSelect (k+3) base a b c n top reserve) (3*n+1)
      (cfgSelect (k+6) base a b (c+n) 0 top (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing c reserve with
  | zero => simpa using WordEventSystem.Block.single graphSystem (child_zero_s_move k rows base a b c 0 top reserve)
  | succ n ih =>
    have h1 := WordEventSystem.Block.single graphSystem (child_dec_s_move k rows base a b c n top reserve)
    have h2 := WordEventSystem.Block.single graphSystem (child_inc_c k rows base a b c n top (reserve ++ [0]))
    have h3 := WordEventSystem.Block.single graphSystem (child_jump5 k rows base a b (c+1) n top (reserve ++ [0]))
    have h := ((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem (ih (c+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem child_clear_scratch (n k : Nat) (rows : ChildSelectRows k) (base : RegisterMachine.Bank 9)
    (a b c top : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgSelect (k+7) base a b c n top reserve) (2*n+1)
      (cfgSelect (k+9) base a b c 0 top (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing reserve with
  | zero => simpa using WordEventSystem.Block.single graphSystem (child_zero_s_clear k rows base a b c 0 top reserve)
  | succ n ih =>
    have h1 := WordEventSystem.Block.single graphSystem (child_dec_s_clear k rows base a b c n top reserve)
    have h2 := WordEventSystem.Block.single graphSystem (child_jump8 k rows base a b c n top (reserve ++ [0]))
    have h := (h1.trans graphSystem h2).trans graphSystem (ih (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem child_move_c_top (n k : Nat) (rows : ChildSelectRows k) (base : RegisterMachine.Bank 9)
    (a b scratch top : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgSelect (k+9) base a b n scratch top reserve) (3*n+1)
      (cfgSelect (k+12) base a b 0 scratch (top+n) (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing top reserve with
  | zero => simpa using WordEventSystem.Block.single graphSystem (child_zero_c_top k rows base a b 0 scratch top reserve)
  | succ n ih =>
    have h1 := WordEventSystem.Block.single graphSystem (child_dec_c_top k rows base a b n scratch top reserve)
    have h2 := WordEventSystem.Block.single graphSystem (child_inc_top k rows base a b n scratch top (reserve ++ [0]))
    have h3 := WordEventSystem.Block.single graphSystem (child_jump11 k rows base a b n scratch (top+1) (reserve ++ [0]))
    have h := ((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem (ih (top+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

/-- For move zero, discard scratch and add the tag to top; all other
registers, including any pre-existing top, are tracked exactly. -/
theorem child_select_zero (k : Nat) (rows : ChildSelectRows k) (base : RegisterMachine.Bank 9)
    (b tag payload top : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgSelect k base 0 b tag payload top reserve) (2*payload+3*tag+3)
      (cfgSelect (k+12) base 0 b 0 0 (top+tag)
        (reserve ++ List.replicate (payload+tag) 0)) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (child_zero_a k rows base 0 b tag payload top reserve)
  have h2 := child_clear_scratch payload k rows base 0 b tag top reserve
  have h3 := child_move_c_top tag k rows base 0 b 0 top (reserve ++ List.replicate payload 0)
  have h := (h1.trans graphSystem h2).trans graphSystem h3
  have hr : (reserve ++ List.replicate payload 0) ++ List.replicate tag 0 =
      reserve ++ List.replicate (payload+tag) 0 := by
    simp only [List.append_assoc, ← List.replicate_add]
  rw [hr] at h
  have ht : 1+(2*payload+1)+(3*tag+1) = 2*payload+3*tag+3 := by omega
  simpa [ht] using h

/-- For a positive move, discard the tag, move the payload to top, and retain
the decremented move for the environment pairing. -/
theorem child_select_positive (k : Nat) (rows : ChildSelectRows k) (base : RegisterMachine.Bank 9)
    (move b tag payload top : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgSelect k base (move+1) b tag payload top reserve) (2*tag+6*payload+5)
      (cfgSelect (k+12) base move b 0 0 (top+payload)
        (reserve ++ List.replicate (1+tag+2*payload) 0)) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (child_dec_a k rows base move b tag payload top reserve)
  have h2 := child_clear_c tag k rows base move b payload top (reserve ++ [0])
  have h3 := child_move_scratch payload k rows base move b 0 top ((reserve ++ [0]) ++ List.replicate tag 0)
  simp only [Nat.zero_add] at h3
  have h4 := WordEventSystem.Block.single graphSystem (child_jump6 k rows base move b payload 0 top
    (((reserve ++ [0]) ++ List.replicate tag 0) ++ List.replicate payload 0))
  have h5 := child_move_c_top payload k rows base move b 0 top
    ((((reserve ++ [0]) ++ List.replicate tag 0) ++ List.replicate payload 0))
  have h := (((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4).trans graphSystem h5
  have hr : ((((reserve ++ [0]) ++ List.replicate tag 0) ++ List.replicate payload 0) ++ List.replicate payload 0) =
      reserve ++ List.replicate (1+tag+2*payload) 0 := by
    change ((((reserve ++ List.replicate 1 0) ++ List.replicate tag 0) ++ List.replicate payload 0) ++ List.replicate payload 0) = _
    have heq : 1+tag+2*payload = 1+tag+payload+payload := by omega
    rw [heq]
    simp only [List.append_assoc, ← List.replicate_add]
  rw [hr] at h
  have ht : 1+(2*tag+1)+(3*payload+1)+1+(3*payload+1) = 2*tag+6*payload+5 := by omega
  simpa [ht] using h

def childChoice (move tag payload : Nat) : Nat := if move = 0 then tag else payload

/-- Both finite selector branches, for arbitrary move, tag, payload and top. -/
theorem child_select (k : Nat) (rows : ChildSelectRows k) (base : RegisterMachine.Bank 9)
    (move b tag payload top : Nat) (reserve : List Nat) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block (cfgSelect k base move b tag payload top reserve) duration
        (cfgSelect (k+12) base (move-1) b 0 0 (top+childChoice move tag payload)
          (reserve ++ List.replicate padding 0)) [] := by
  cases move with
  | zero =>
    refine ⟨2*payload+3*tag+3, payload+tag, by omega, ?_⟩
    simpa [childChoice] using child_select_zero k rows base b tag payload top reserve
  | succ move =>
    refine ⟨2*tag+6*payload+5, 1+tag+2*payload, by omega, ?_⟩
    simpa [childChoice] using child_select_positive k rows base move b tag payload top reserve

/-- Change only the bank view: selection leaves the counter and environment
unchanged while exposing the clean c register to the pairing routine. -/
theorem child_select_to_pair_view (i : Nat) (base : RegisterMachine.Bank 9)
    (a b c scratch top : Nat) (reserve : List Nat) :
    cfgSelect i base a b c scratch top reserve =
      cfgBudget i (bankSelect base a b c scratch top) (base 3) (base 5) a c reserve := by
  unfold cfgSelect cfgBudget
  congr 1
  funext i
  fin_cases i <;> simp [bankSelect, bankHalf, bankBudget, RegisterMachine.write]

/-- Child selection followed by environment pairing is a silent finite graph
block. The old top is added to the selected child; no zero-top assumption is
hidden. -/
theorem child_select_pair (k : Nat) (rows : ChildSelectRows k) (pairRows : PairEnvRows (k+12))
    (base : RegisterMachine.Bank 9) (move b tag payload top : Nat) (reserve : List Nat) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block (cfgSelect k base move b tag payload top reserve) duration
        (cfgBudget (k+25) (bankSelect base (move-1) b 0 0 (top+childChoice move tag payload))
          (base 3) (Cantor.pair (move-1) (base 5)) 0 0 (reserve ++ List.replicate padding 0)) [] := by
  obtain ⟨d1, p1, hd1, h1⟩ := child_select k rows base move b tag payload top reserve
  rw [child_select_to_pair_view (k+12) base (move-1) b 0 0 (top+childChoice move tag payload) _] at h1
  obtain ⟨d2, p2, hd2, h2⟩ := pair_environment (k+12) pairRows
    (bankSelect base (move-1) b 0 0 (top+childChoice move tag payload))
    (base 3) (base 5) (move-1) (reserve ++ List.replicate p1 0)
  have h := h1.trans graphSystem h2
  refine ⟨d1+d2, p1+p2, by omega, ?_⟩
  have hr : (reserve ++ List.replicate p1 0) ++ List.replicate p2 0 =
      reserve ++ List.replicate (p1+p2) 0 := by
    simp only [List.append_assoc, ← List.replicate_add]
  rw [hr] at h
  simpa [Nat.add_assoc] using h

structure ChildNextRow (k dest : Nat) : Prop where
  jump : sourceRows[k+25]? = some ("jump", dest, none)

theorem child_next_225 : ChildNextRow 225 366 := ⟨by decide⟩
theorem child_next_402 : ChildNextRow 402 546 := ⟨by decide⟩
theorem child_next_582 : ChildNextRow 582 723 := ⟨by decide⟩

theorem child_next_step (k dest : Nat) (row : ChildNextRow k dest)
    (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget (k+25) base count env a c reserve) =
      (cfgBudget dest base count env a c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, row.jump, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

/-- The prepared child-and-environment update through its checked continuation. -/
theorem child_select_pair_continue (k dest : Nat) (rows : ChildSelectRows k)
    (pairRows : PairEnvRows (k+12)) (next : ChildNextRow k dest)
    (base : RegisterMachine.Bank 9) (move b tag payload top : Nat) (reserve : List Nat) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block (cfgSelect k base move b tag payload top reserve) duration
        (cfgBudget dest (bankSelect base (move-1) b 0 0 (top+childChoice move tag payload))
          (base 3) (Cantor.pair (move-1) (base 5)) 0 0 (reserve ++ List.replicate padding 0)) [] := by
  obtain ⟨duration, padding, ht, h1⟩ := child_select_pair k rows pairRows base move b tag payload top reserve
  have h2 := WordEventSystem.Block.single graphSystem
    (child_next_step k dest next (bankSelect base (move-1) b 0 0 (top+childChoice move tag payload))
      (base 3) (Cantor.pair (move-1) (base 5)) 0 0 (reserve ++ List.replicate padding 0))
  exact ⟨duration+1, padding, by omega, by simpa using h1.trans graphSystem h2⟩

/-- The graph's local branch choice agrees with the abstract child operation;
this arithmetic identification does not claim a Python compiler refinement. -/
theorem child_choice_eq_abstract (formula move : Nat) :
    childChoice move ((Cantor.unpair formula).1-1) (Cantor.unpair formula).2 =
      M236Game.child formula move := by
  simp [childChoice, M236Game.child, M236Game.tag, M236Game.payload]

/-- At the prepared row-402 nonzero-tag entry, zero initial top gives exactly
the abstract child and pairs the consumed move with the old environment. -/
theorem positive_tag_child_update (formula move b : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (_htag : (Cantor.unpair formula).1 ≠ 0) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block (cfgSelect 402 base move b ((Cantor.unpair formula).1-1) (Cantor.unpair formula).2 0 reserve) duration
        (cfgBudget 546 (bankSelect base (move-1) b 0 0 (M236Game.child formula move))
          (base 3) (Cantor.pair (move-1) (base 5)) 0 0 (reserve ++ List.replicate padding 0)) [] := by
  have h := child_select_pair_continue 402 546 child_rows_402 pair_env_rows_414 child_next_402
    base move b ((Cantor.unpair formula).1-1) (Cantor.unpair formula).2 0 reserve
  simpa [child_choice_eq_abstract] using h

/-- The selector view uses the old bank's exact top register. -/
theorem half_to_child_view (i : Nat) (base : RegisterMachine.Bank 9)
    (a b c scratch : Nat) (reserve : List Nat) :
    cfgHalf i base a b c scratch reserve = cfgSelect i base a b c scratch (base 4) reserve := by
  unfold cfgHalf cfgSelect bankSelect
  congr 1
  funext i
  fin_cases i <;> simp [bankHalf, RegisterMachine.write]

/-- A prepared formula at row 393 with nonzero Cantor tag and zero top is
scanned, dispatched, and updated through row 546. The child and paired
environment agree with the abstract encoded evaluator's single non-atomic
step; this does not establish an infinite evaluator simulation. -/
theorem positive_formula_child_update (formula move : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (htag : (Cantor.unpair formula).1 ≠ 0) (htop : base 4 = 0) :
    ∃ duration padding, formula+2 ≤ duration ∧
      graphSystem.Block (cfgHalf 393 base move formula 0 0 reserve) duration
        (cfgBudget 546 (bankSelect base (move-1) 0 0 0 (M236Game.child formula move))
          (base 3) (Cantor.pair (move-1) (base 5)) 0 0 (reserve ++ List.replicate padding 0)) [] := by
  have htag' : (Cantor.unpair formula).1 = ((Cantor.unpair formula).1-1)+1 := by omega
  obtain ⟨d1, p1, hd1, h1⟩ := formula_unpair_positive_branch move formula 393
    ((Cantor.unpair formula).1-1) formula_scan_rows_393 formula_branch_row_393 base reserve htag'
  rw [half_to_child_view 402 base move 0 ((Cantor.unpair formula).1-1) (Cantor.unpair formula).2 _, htop] at h1
  obtain ⟨d2, p2, hd2, h2⟩ := positive_tag_child_update formula move 0 base
    (reserve ++ List.replicate p1 0) htag
  have h := h1.trans graphSystem h2
  refine ⟨d1+d2, p1+p2, by omega, ?_⟩
  have hr : (reserve ++ List.replicate p1 0) ++ List.replicate p2 0 =
      reserve ++ List.replicate (p1+p2) 0 := by
    simp only [List.append_assoc, ← List.replicate_add]
  rw [hr] at h
  simpa using h

/-- Register projection of the prepared non-atomic update's exact endpoint. -/
theorem positive_child_exit_registers (formula move : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) :
    let s := cfgBudget 546 (bankSelect base (move-1) 0 0 0 (M236Game.child formula move))
      (base 3) (Cantor.pair (move-1) (base 5)) 0 0 reserve
    s.registers 0 = 0 ∧ s.registers 1 = base 1 ∧ s.registers 2 = base 2 ∧
    s.registers 3 = base 3 ∧ s.registers 4 = M236Game.child formula move ∧
    s.registers 5 = Cantor.pair (move-1) (base 5) ∧
    s.registers 6 = 0 ∧ s.registers 7 = 0 ∧ s.registers 8 = 0 := by
  simp [cfgBudget, bankSelect, bankHalf, bankBudget, RegisterMachine.write]

/-- Physical lift conditional on reaching the prepared row-393 state. -/
theorem selected_positive_formula_child_update (i formula move : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (htag : (Cantor.unpair formula).1 ≠ 0) (htop : base 4 = 0)
    (h : graphSystem.run i = cfgHalf 393 base move formula 0 0 reserve) :
    ∃ duration padding finish, formula+2 ≤ duration ∧ Good finish ∧
      finish.graphState = cfgBudget 546 (bankSelect base (move-1) 0 0 0 (M236Game.child formula move))
        (base 3) (Cantor.pair (move-1) (base 5)) 0 0 (reserve ++ List.replicate padding 0) ∧
      graphSystem.run (i+duration) = cfgBudget 546 (bankSelect base (move-1) 0 0 0 (M236Game.child formula move))
        (base 3) (Cantor.pair (move-1) (base 5)) 0 0 (reserve ++ List.replicate padding 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run (graphRefinement.boundary (i+duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i+duration) := by
  obtain ⟨duration, padding, ht, block⟩ := positive_formula_child_update formula move base reserve htag htop
  have hr : graphSystem.run (i+duration) = cfgBudget 546 (bankSelect base (move-1) 0 0 0 (M236Game.child formula move))
      (base 3) (Cantor.pair (move-1) (base 5)) 0 0 (reserve ++ List.replicate padding 0) := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i+duration) = graphSystem.prefixWord i := by
    rw [WordEventSystem.prefix_add, h, block.output, List.append_nil]
  obtain ⟨finish, hg, hstate, hconfig⟩ := graphRefinement.related (i+duration)
  refine ⟨duration, padding, finish, ht, hg, hstate.trans hr, hr, hconfig, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

end PASoundness.M236.OccurrenceGraph
