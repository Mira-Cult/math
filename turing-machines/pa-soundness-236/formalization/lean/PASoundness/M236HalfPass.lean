import PASoundness.M236CoordinateBudget

/-! The checked graph's half pass in the bounded-coordinate bit routine.
The producer pinned at `bad500e2d22c3f8b7c6420f5c5b1a504a6a57b30`
uses `SpentRank.unsigned_prefix` in `pa266-architecture-20261031/spent_rank.py`
and `bit_b_a` in `pa576-architecture-20261031/bit_cursor.py`. These graph
theorems do not prove the Python producer-to-graph correspondence. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

def bankHalf (base : RegisterMachine.Bank 9) (a b c scratch : Nat) : RegisterMachine.Bank 9 :=
  fun i => if i = 0 then scratch else if i = 6 then a else if i = 7 then b else if i = 8 then c else base i

def cfgHalf (i : Nat) (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) : GraphState :=
  ⟨i, bankHalf base a b c scratch, reserve⟩

theorem half_row119 : sourceRows[119]? = some ("3.k.a.decnz", 120, some 133) := by decide
theorem half_row120 : sourceRows[120]? = some ("3.k.b.decnz", 121, some 127) := by decide
theorem half_row121 : sourceRows[121]? = some ("3.scratch.copy.inc", 122, none) := by decide
theorem half_row122 : sourceRows[122]? = some ("3.k.b.decnz", 123, some 126) := by decide
theorem half_row123 : sourceRows[123]? = some ("3.scratch.copy.decnz", 124, some 125) := by decide
theorem half_row124 : sourceRows[124]? = some ("jump", 123, none) := by decide
theorem half_row125 : sourceRows[125]? = some ("3.k.c.inc", 126, none) := by decide
theorem half_row126 : sourceRows[126]? = some ("jump", 120, none) := by decide
theorem half_row127 : sourceRows[127]? = some ("3.k.c.decnz", 128, some 130) := by decide
theorem half_row128 : sourceRows[128]? = some ("3.k.b.inc", 129, none) := by decide
theorem half_row129 : sourceRows[129]? = some ("jump", 127, none) := by decide
theorem half_row130 : sourceRows[130]? = some ("3.scratch.copy.decnz", 131, some 132) := by decide
theorem half_row131 : sourceRows[131]? = some ("jump", 130, none) := by decide
theorem half_row132 : sourceRows[132]? = some ("jump", 119, none) := by decide

theorem half_a_dec (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 119 base (a+1) (b) (c) (scratch) reserve) =
      (cfgHalf 120 base (a) (b) (c) (scratch) (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgHalf, half_row119, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem half_a_zero (base : RegisterMachine.Bank 9) (_a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 119 base (0) (b) (c) (scratch) reserve) =
      (cfgHalf 133 base (0) (b) (c) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, half_row119, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem half_b_dec_120 (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 120 base (a) (b+1) (c) (scratch) reserve) =
      (cfgHalf 121 base (a) (b) (c) (scratch) (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgHalf, half_row120, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem half_b_zero_120 (base : RegisterMachine.Bank 9) (a _b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 120 base (a) (0) (c) (scratch) reserve) =
      (cfgHalf 127 base (a) (0) (c) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, half_row120, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem half_inc_scratch (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 121 base (a) (b) (c) (scratch) reserve) =
      (cfgHalf 122 base (a) (b) (c) (scratch+1) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, half_row121, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem half_b_dec_122 (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 122 base (a) (b+1) (c) (scratch) reserve) =
      (cfgHalf 123 base (a) (b) (c) (scratch) (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgHalf, half_row122, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem half_b_zero_122 (base : RegisterMachine.Bank 9) (a _b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 122 base (a) (0) (c) (scratch) reserve) =
      (cfgHalf 126 base (a) (0) (c) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, half_row122, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem half_scratch_dec_123 (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 123 base (a) (b) (c) (scratch+1) reserve) =
      (cfgHalf 124 base (a) (b) (c) (scratch) (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgHalf, half_row123, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem half_scratch_zero_123 (base : RegisterMachine.Bank 9) (a b c _scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 123 base (a) (b) (c) (0) reserve) =
      (cfgHalf 125 base (a) (b) (c) (0) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, half_row123, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem half_jump124 (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 124 base (a) (b) (c) (scratch) reserve) =
      (cfgHalf 123 base (a) (b) (c) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, half_row124, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem half_inc_c (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 125 base (a) (b) (c) (scratch) reserve) =
      (cfgHalf 126 base (a) (b) (c+1) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, half_row125, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem half_jump126 (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 126 base (a) (b) (c) (scratch) reserve) =
      (cfgHalf 120 base (a) (b) (c) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, half_row126, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem half_c_dec (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 127 base (a) (b) (c+1) (scratch) reserve) =
      (cfgHalf 128 base (a) (b) (c) (scratch) (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgHalf, half_row127, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem half_c_zero (base : RegisterMachine.Bank 9) (a b _c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 127 base (a) (b) (0) (scratch) reserve) =
      (cfgHalf 130 base (a) (b) (0) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, half_row127, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem half_inc_b (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 128 base (a) (b) (c) (scratch) reserve) =
      (cfgHalf 129 base (a) (b+1) (c) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, half_row128, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem half_jump129 (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 129 base (a) (b) (c) (scratch) reserve) =
      (cfgHalf 127 base (a) (b) (c) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, half_row129, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem half_scratch_dec_130 (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 130 base (a) (b) (c) (scratch+1) reserve) =
      (cfgHalf 131 base (a) (b) (c) (scratch) (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgHalf, half_row130, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem half_scratch_zero_130 (base : RegisterMachine.Bank 9) (a b c _scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 130 base (a) (b) (c) (0) reserve) =
      (cfgHalf 132 base (a) (b) (c) (0) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, half_row130, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem half_jump131 (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 131 base (a) (b) (c) (scratch) reserve) =
      (cfgHalf 130 base (a) (b) (c) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, half_row131, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem half_jump132 (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 132 base (a) (b) (c) (scratch) reserve) =
      (cfgHalf 119 base (a) (b) (c) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, half_row132, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]


/-- Two `b` units produce one `c` unit, clear scratch and add three
zero reserve blocks. -/
theorem half_pair_cycle (base : RegisterMachine.Bank 9) (a b c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf 120 base a (b+2) c 0 reserve) 8
      (cfgHalf 120 base a b (c+1) 0 (reserve ++ [0,0,0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (half_b_dec_120 base a (b+1) c 0 reserve)
  have h2 := WordEventSystem.Block.single graphSystem (half_inc_scratch base a (b+1) c 0 (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (half_b_dec_122 base a b c 1 (reserve ++ [0]))
  have h4 := WordEventSystem.Block.single graphSystem (half_scratch_dec_123 base a b c 0 ((reserve ++ [0]) ++ [0]))
  have h5 := WordEventSystem.Block.single graphSystem (half_jump124 base a b c 0 (((reserve ++ [0]) ++ [0]) ++ [0]))
  have h6 := WordEventSystem.Block.single graphSystem (half_scratch_zero_123 base a b c 0 (((reserve ++ [0]) ++ [0]) ++ [0]))
  have h7 := WordEventSystem.Block.single graphSystem (half_inc_c base a b c 0 (((reserve ++ [0]) ++ [0]) ++ [0]))
  have h8 := WordEventSystem.Block.single graphSystem (half_jump126 base a b (c+1) 0 (((reserve ++ [0]) ++ [0]) ++ [0]))
  simpa [List.append_assoc] using ((((((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4).trans graphSystem h5).trans graphSystem h6).trans graphSystem h7).trans graphSystem h8

theorem half_scan_pairs (n : Nat) (base : RegisterMachine.Bank 9) (a r c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf 120 base a (2*n+r) c 0 reserve) (8*n)
      (cfgHalf 120 base a r (c+n) 0 (reserve ++ List.replicate (3*n) 0)) [] := by
  induction n generalizing c reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgHalf 120 base a r c 0 reserve)
  | succ n ih =>
    have h := (half_pair_cycle base a (2*n+r) c reserve).trans graphSystem (ih (c+1) (reserve ++ [0,0,0]))
    have hr : (reserve ++ [0,0,0]) ++ List.replicate (3*n) 0 =
        reserve ++ List.replicate (3*(n+1)) 0 := by
      have hn : 3*(n+1) = 3+3*n := by omega
      rw [hn, List.replicate_add]
      simp [List.replicate_succ, List.append_assoc]
    rw [hr] at h
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem half_restore_all (n : Nat) (base : RegisterMachine.Bank 9) (a b scratch : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf 127 base a b n scratch reserve) (3*n)
      (cfgHalf 127 base a (b+n) 0 scratch (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing b reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgHalf 127 base a b 0 scratch reserve)
  | succ n ih =>
    have h1 := WordEventSystem.Block.single graphSystem (half_c_dec base a b n scratch reserve)
    have h2 := WordEventSystem.Block.single graphSystem (half_inc_b base a b n scratch (reserve ++ [0]))
    have h3 := WordEventSystem.Block.single graphSystem (half_jump129 base a (b+1) n scratch (reserve ++ [0]))
    have h := ((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem (ih (b+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem half_clear_scratch (n : Nat) (base : RegisterMachine.Bank 9) (a b c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf 130 base a b c n reserve) (2*n+1)
      (cfgHalf 132 base a b c 0 (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing reserve with
  | zero => simpa using WordEventSystem.Block.single graphSystem (half_scratch_zero_130 base a b c 0 reserve)
  | succ n ih =>
    have h1 := WordEventSystem.Block.single graphSystem (half_scratch_dec_130 base a b c n reserve)
    have h2 := WordEventSystem.Block.single graphSystem (half_jump131 base a b c n (reserve ++ [0]))
    have h := (h1.trans graphSystem h2).trans graphSystem (ih (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

/-- For an even input, a half pass takes exactly `11*n+4` graph steps,
appends `4*n` zero reserve blocks, and emits nothing. -/
theorem half_pass_even (n : Nat) (base : RegisterMachine.Bank 9) (a : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf 120 base a (2*n) 0 0 reserve) (11*n+4)
      (cfgHalf 119 base a n 0 0 (reserve ++ List.replicate (4*n) 0)) [] := by
  have h1 : graphSystem.Block (cfgHalf 120 base a (2*n) 0 0 reserve) (8*n)
      (cfgHalf 120 base a 0 n 0 (reserve ++ List.replicate (3*n) 0)) [] := by
    simpa using half_scan_pairs n base a 0 0 reserve
  have h2 := WordEventSystem.Block.single graphSystem (half_b_zero_120 base a 0 n 0 (reserve ++ List.replicate (3*n) 0))
  have h3 := half_restore_all n base a 0 0 (reserve ++ List.replicate (3*n) 0)
  simp only [Nat.zero_add] at h3
  have h4 := WordEventSystem.Block.single graphSystem (half_c_zero base a n 0 0 ((reserve ++ List.replicate (3*n) 0) ++ List.replicate n 0))
  have h5 := WordEventSystem.Block.single graphSystem (half_scratch_zero_130 base a n 0 0 ((reserve ++ List.replicate (3*n) 0) ++ List.replicate n 0))
  have h6 := WordEventSystem.Block.single graphSystem (half_jump132 base a n 0 0 ((reserve ++ List.replicate (3*n) 0) ++ List.replicate n 0))
  have h := ((((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4).trans graphSystem h5).trans graphSystem h6
  have hr : (reserve ++ List.replicate (3*n) 0) ++ List.replicate n 0 = reserve ++ List.replicate (4*n) 0 := by
    have heq : 4*n = 3*n+n := by omega
    rw [heq, List.replicate_add, List.append_assoc]
  rw [hr] at h
  have ht : 8*n+1+3*n+1+1+1 = 11*n+4 := by omega
  simpa [ht] using h

/-- The odd case clears the remainder after the quotient is restored. -/
theorem half_pass_odd (n : Nat) (base : RegisterMachine.Bank 9) (a : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf 120 base a (2*n+1) 0 0 reserve) (11*n+10)
      (cfgHalf 119 base a n 0 0 (reserve ++ List.replicate (4*n+2) 0)) [] := by
  have h1 : graphSystem.Block (cfgHalf 120 base a (2*n+1) 0 0 reserve) (8*n)
      (cfgHalf 120 base a 1 n 0 (reserve ++ List.replicate (3*n) 0)) [] := by
    simpa using half_scan_pairs n base a 1 0 reserve
  let r := reserve ++ List.replicate (3*n) 0
  have h2 := WordEventSystem.Block.single graphSystem (half_b_dec_120 base a 0 n 0 r)
  have h3 := WordEventSystem.Block.single graphSystem (half_inc_scratch base a 0 n 0 (r ++ [0]))
  have h4 := WordEventSystem.Block.single graphSystem (half_b_zero_122 base a 0 n 1 (r ++ [0]))
  have h5 := WordEventSystem.Block.single graphSystem (half_jump126 base a 0 n 1 (r ++ [0]))
  have h6 := WordEventSystem.Block.single graphSystem (half_b_zero_120 base a 0 n 1 (r ++ [0]))
  have h7 := half_restore_all n base a 0 1 (r ++ [0])
  simp only [Nat.zero_add] at h7
  let s := (r ++ [0]) ++ List.replicate n 0
  have h8 := WordEventSystem.Block.single graphSystem (half_c_zero base a n 0 1 s)
  have h9 := half_clear_scratch 1 base a n 0 s
  have h10 := WordEventSystem.Block.single graphSystem (half_jump132 base a n 0 0 (s ++ [0]))
  have h := ((((((((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4).trans graphSystem h5).trans graphSystem h6).trans graphSystem h7).trans graphSystem h8).trans graphSystem h9).trans graphSystem h10
  have hr : s ++ [0] = reserve ++ List.replicate (4*n+2) 0 := by
    dsimp [s, r]
    change (((reserve ++ List.replicate (3*n) 0) ++ List.replicate 1 0) ++ List.replicate n 0) ++ List.replicate 1 0 = _
    have heq : 4*n+2 = 3*n+1+n+1 := by omega
    rw [heq]
    simp only [List.append_assoc, ← List.replicate_add]
  rw [hr] at h
  have ht : 8*n+1+1+1+1+1+3*n+1+(2*1+1)+1 = 11*n+10 := by omega
  simpa [ht, s, r] using h

/-- Arbitrary natural input, with exact quotient, parity-dependent time and
reserve growth; no event is emitted. -/
theorem half_pass (b : Nat) (base : RegisterMachine.Bank 9) (a : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf 120 base a b 0 0 reserve) (11*(b/2)+4+6*(b%2))
      (cfgHalf 119 base a (b/2) 0 0 (reserve ++ List.replicate (2*b) 0)) [] := by
  have hm : b%2 = 0 ∨ b%2 = 1 := by omega
  rcases hm with hm | hm
  · have hb : b = 2*(b/2) := by omega
    have hr : 2*b = 4*(b/2) := by omega
    simp only [hm, Nat.mul_zero, Nat.add_zero, hr]
    simpa only [← hb] using half_pass_even (b/2) base a reserve
  · have hb : b = 2*(b/2)+1 := by omega
    have hr : 2*b = 4*(b/2)+2 := by omega
    simp only [hm, Nat.mul_one, hr]
    simpa only [← hb, show 4+6 = 10 by decide, Nat.add_assoc] using half_pass_odd (b/2) base a reserve

/-- A positive `a` at entry 119 performs one exact silent right shift of `b`.
The prepared work registers `c` and scratch are zero. -/
theorem half_step (a b : Nat) (base : RegisterMachine.Bank 9) (reserve : List Nat) :
    graphSystem.Block (cfgHalf 119 base (a+1) b 0 0 reserve) (11*(b/2)+5+6*(b%2))
      (cfgHalf 119 base a (b/2) 0 0 (reserve ++ List.replicate (2*b+1) 0)) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (half_a_dec base a b 0 0 reserve)
  have h2 := half_pass b base a (reserve ++ [0])
  have h := h1.trans graphSystem h2
  have hr : (reserve ++ [0]) ++ List.replicate (2*b) 0 =
      reserve ++ List.replicate (2*b+1) 0 := by
    have heq : 2*b+1 = 1+2*b := by omega
    rw [heq, List.replicate_add]
    simp [List.append_assoc]
  rw [hr] at h
  have ht : 1+(11*(b/2)+4+6*(b%2)) = 11*(b/2)+5+6*(b%2) := by omega
  simpa [ht] using h

/-- A successful coordinate-budget exit with clean scratch is a valid entry
for the halving routine. -/
theorem budget_exit_to_half (base : RegisterMachine.Bank 9) (count env a : Nat)
    (reserve : List Nat) (hs : base 0 = 0) :
    cfgBudget 119 base count env a 0 reserve =
      cfgHalf 119 (bankBudget base count env a 0) a (base 7) 0 0 reserve := by
  unfold cfgBudget cfgHalf
  congr 1
  funext i
  fin_cases i <;> simp [bankBudget, bankHalf, hs]

/-- Connect the successful budget scan directly to its first halving pass,
when the selected coordinate is positive. -/
theorem budget_success_then_half (a remaining : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hc : base 8 = 0) (hcount : base 3 = remaining+(a+1)) :
    graphSystem.Block (cfgAS 103 base (a+1) 0 reserve)
      ((10*(a+1)+2) + (11*((base 7)/2)+5+6*((base 7)%2)))
      (cfgHalf 119 (bankBudget (bankAS base (a+1) 0) (base 3) (base 5+(a+1)) (a+1) 0)
        a ((base 7)/2) 0 0
        ((((reserve ++ List.replicate (2*(a+1)) 0) ++ List.replicate (a+1) 0) ++
          List.replicate (2*(base 7)+1) 0))) [] := by
  have h1 := emitted_coordinate_budget_success (a+1) remaining base reserve hc hcount
  have hs : bankAS base (a+1) 0 0 = 0 := by simp [bankAS]
  rw [budget_exit_to_half (bankAS base (a+1) 0) (base 3) (base 5+(a+1)) (a+1) _ hs] at h1
  have h2 := half_step a (base 7)
    (bankBudget (bankAS base (a+1) 0) (base 3) (base 5+(a+1)) (a+1) 0)
    ((reserve ++ List.replicate (2*(a+1)) 0) ++ List.replicate (a+1) 0)
  simpa [bankAS] using h1.trans graphSystem h2

/-- Physical lift of one halving step at an explicitly reached graph entry. -/
theorem selected_half_step (i a b : Nat) (base : RegisterMachine.Bank 9) (reserve : List Nat)
    (h : graphSystem.run i = cfgHalf 119 base (a+1) b 0 0 reserve) :
    ∃ finish, Good finish ∧
      finish.graphState = cfgHalf 119 base a (b/2) 0 0 (reserve ++ List.replicate (2*b+1) 0) ∧
      graphSystem.run (i + (11*(b/2)+5+6*(b%2))) =
        cfgHalf 119 base a (b/2) 0 0 (reserve ++ List.replicate (2*b+1) 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i + (11*(b/2)+5+6*(b%2)))) ∧
      (machineWordSystem machine machineLabels).prefixWord
        (graphRefinement.boundary (i + (11*(b/2)+5+6*(b%2)))) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i + (11*(b/2)+5+6*(b%2))) := by
  have block := half_step a b base reserve
  have hr : graphSystem.run (i + (11*(b/2)+5+6*(b%2))) =
      cfgHalf 119 base a (b/2) 0 0 (reserve ++ List.replicate (2*b+1) 0) := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i + (11*(b/2)+5+6*(b%2))) = graphSystem.prefixWord i := by
    rw [WordEventSystem.prefix_add, h, block.output, List.append_nil]
  obtain ⟨finish, hg, hs, hconfig⟩ := graphRefinement.related (i + (11*(b/2)+5+6*(b%2)))
  refine ⟨finish, hg, hs.trans hr, hr, hconfig, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

end PASoundness.M236.OccurrenceGraph
