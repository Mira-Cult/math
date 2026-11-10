import PASoundness.M236HalfPass

/-! Iterated graph right shifts for the bounded-coordinate bit routine. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

/-- Arbitrarily many prepared halving passes take finite time, positive when
the number of passes is positive, with exact quotient and all untouched
registers retained. The padding consists
only of zero reserve blocks; its total length depends on the input. -/
theorem half_repeated (n b : Nat) (base : RegisterMachine.Bank 9) (reserve : List Nat) :
    ∃ duration padding, n ≤ duration ∧
      graphSystem.Block (cfgHalf 119 base n b 0 0 reserve) duration
        (cfgHalf 119 base 0 (b / 2^n) 0 0 (reserve ++ List.replicate padding 0)) [] := by
  induction n generalizing b reserve with
  | zero =>
    refine ⟨0, 0, by omega, ?_⟩
    simpa using WordEventSystem.Block.refl graphSystem (cfgHalf 119 base 0 b 0 0 reserve)
  | succ n ih =>
    have h1 := half_step n b base reserve
    obtain ⟨duration, padding, ht, h2⟩ := ih (b/2) (reserve ++ List.replicate (2*b+1) 0)
    have h := h1.trans graphSystem h2
    refine ⟨(11*(b/2)+5+6*(b%2))+duration, (2*b+1)+padding, by omega, ?_⟩
    have hr : (reserve ++ List.replicate (2*b+1) 0) ++ List.replicate padding 0 =
        reserve ++ List.replicate ((2*b+1)+padding) 0 := by
      simp only [List.append_assoc, ← List.replicate_add]
    rw [hr] at h
    simpa [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm] using h

/-- Once all shifts finish, the zero branch enters the parity extractor. -/
theorem half_repeated_to_parity (n b : Nat) (base : RegisterMachine.Bank 9) (reserve : List Nat) :
    ∃ duration padding, n+1 ≤ duration ∧
      graphSystem.Block (cfgHalf 119 base n b 0 0 reserve) duration
        (cfgHalf 133 base 0 (b / 2^n) 0 0 (reserve ++ List.replicate padding 0)) [] := by
  obtain ⟨duration, padding, ht, h⟩ := half_repeated n b base reserve
  have hzero := WordEventSystem.Block.single graphSystem
    (half_a_zero base 0 (b / 2^n) 0 0 (reserve ++ List.replicate padding 0))
  refine ⟨duration+1, padding, by omega, ?_⟩
  simpa using h.trans graphSystem hzero

theorem parity_row133 : sourceRows[133]? = some ("3.k.b.decnz", 134, some 140) := by decide
theorem parity_row134 : sourceRows[134]? = some ("3.scratch.copy.inc", 135, none) := by decide
theorem parity_row135 : sourceRows[135]? = some ("3.k.b.decnz", 136, some 139) := by decide
theorem parity_row136 : sourceRows[136]? = some ("3.scratch.copy.decnz", 137, some 138) := by decide
theorem parity_row137 : sourceRows[137]? = some ("jump", 136, none) := by decide
theorem parity_row138 : sourceRows[138]? = some ("3.k.c.inc", 139, none) := by decide
theorem parity_row139 : sourceRows[139]? = some ("jump", 133, none) := by decide
theorem parity_row140 : sourceRows[140]? = some ("3.k.c.decnz", 141, some 142) := by decide
theorem parity_row141 : sourceRows[141]? = some ("jump", 140, none) := by decide
theorem parity_row142 : sourceRows[142]? = some ("3.scratch.copy.decnz", 143, some 145) := by decide
theorem parity_row143 : sourceRows[143]? = some ("3.k.b.inc", 144, none) := by decide
theorem parity_row144 : sourceRows[144]? = some ("jump", 142, none) := by decide

theorem parity_b_dec (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 133 base (a) (b+1) (c) (scratch) reserve) =
      (cfgHalf 134 base (a) (b) (c) (scratch) (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgHalf, parity_row133, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])


theorem parity_b_zero (base : RegisterMachine.Bank 9) (a _b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 133 base (a) (0) (c) (scratch) reserve) =
      (cfgHalf 140 base (a) (0) (c) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, parity_row133, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]


theorem parity_inc_scratch (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 134 base (a) (b) (c) (scratch) reserve) =
      (cfgHalf 135 base (a) (b) (c) (scratch+1) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, parity_row134, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])


theorem parity_b_dec_second (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 135 base (a) (b+1) (c) (scratch) reserve) =
      (cfgHalf 136 base (a) (b) (c) (scratch) (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgHalf, parity_row135, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])


theorem parity_b_zero_second (base : RegisterMachine.Bank 9) (a _b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 135 base (a) (0) (c) (scratch) reserve) =
      (cfgHalf 139 base (a) (0) (c) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, parity_row135, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]


theorem parity_scratch_dec (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 136 base (a) (b) (c) (scratch+1) reserve) =
      (cfgHalf 137 base (a) (b) (c) (scratch) (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgHalf, parity_row136, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])


theorem parity_scratch_zero (base : RegisterMachine.Bank 9) (a b c _scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 136 base (a) (b) (c) (0) reserve) =
      (cfgHalf 138 base (a) (b) (c) (0) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, parity_row136, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]


theorem parity_jump137 (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 137 base (a) (b) (c) (scratch) reserve) =
      (cfgHalf 136 base (a) (b) (c) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, parity_row137, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]


theorem parity_inc_c (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 138 base (a) (b) (c) (scratch) reserve) =
      (cfgHalf 139 base (a) (b) (c+1) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, parity_row138, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])


theorem parity_jump139 (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 139 base (a) (b) (c) (scratch) reserve) =
      (cfgHalf 133 base (a) (b) (c) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, parity_row139, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]


theorem parity_pair_cycle (base : RegisterMachine.Bank 9) (a b c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf 133 base a (b+2) c 0 reserve) 8
      (cfgHalf 133 base a b (c+1) 0 (reserve ++ [0,0,0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (parity_b_dec base a (b+1) c 0 reserve)
  have h2 := WordEventSystem.Block.single graphSystem (parity_inc_scratch base a (b+1) c 0 (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (parity_b_dec_second base a b c 1 (reserve ++ [0]))
  have h4 := WordEventSystem.Block.single graphSystem (parity_scratch_dec base a b c 0 ((reserve ++ [0]) ++ [0]))
  have h5 := WordEventSystem.Block.single graphSystem (parity_jump137 base a b c 0 (((reserve ++ [0]) ++ [0]) ++ [0]))
  have h6 := WordEventSystem.Block.single graphSystem (parity_scratch_zero base a b c 0 (((reserve ++ [0]) ++ [0]) ++ [0]))
  have h7 := WordEventSystem.Block.single graphSystem (parity_inc_c base a b c 0 (((reserve ++ [0]) ++ [0]) ++ [0]))
  have h8 := WordEventSystem.Block.single graphSystem (parity_jump139 base a b (c+1) 0 (((reserve ++ [0]) ++ [0]) ++ [0]))
  simpa [List.append_assoc] using ((((((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4).trans graphSystem h5).trans graphSystem h6).trans graphSystem h7).trans graphSystem h8


theorem parity_scan_pairs (n : Nat) (base : RegisterMachine.Bank 9) (a r c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf 133 base a (2*n+r) c 0 reserve) (8*n)
      (cfgHalf 133 base a r (c+n) 0 (reserve ++ List.replicate (3*n) 0)) [] := by
  induction n generalizing c reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgHalf 133 base a r c 0 reserve)
  | succ n ih =>
    have h := (parity_pair_cycle base a (2*n+r) c reserve).trans graphSystem (ih (c+1) (reserve ++ [0,0,0]))
    have hr : (reserve ++ [0,0,0]) ++ List.replicate (3*n) 0 =
        reserve ++ List.replicate (3*(n+1)) 0 := by
      have hn : 3*(n+1) = 3+3*n := by omega
      rw [hn, List.replicate_add]
      simp [List.replicate_succ, List.append_assoc]
    rw [hr] at h
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h


theorem parity_dec_c (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 140 base (a) (b) (c+1) (scratch) reserve) =
      (cfgHalf 141 base (a) (b) (c) (scratch) (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgHalf, parity_row140, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem parity_zero_c (base : RegisterMachine.Bank 9) (a b _c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 140 base (a) (b) (0) (scratch) reserve) =
      (cfgHalf 142 base (a) (b) (0) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, parity_row140, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem parity_jump141 (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 141 base (a) (b) (c) (scratch) reserve) =
      (cfgHalf 140 base (a) (b) (c) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, parity_row141, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem parity_dec_scratch (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 142 base (a) (b) (c) (scratch+1) reserve) =
      (cfgHalf 143 base (a) (b) (c) (scratch) (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgHalf, parity_row142, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem parity_zero_scratch (base : RegisterMachine.Bank 9) (a b c _scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 142 base (a) (b) (c) (0) reserve) =
      (cfgHalf 145 base (a) (b) (c) (0) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, parity_row142, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem parity_inc_b (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 143 base (a) (b) (c) (scratch) reserve) =
      (cfgHalf 144 base (a) (b+1) (c) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, parity_row143, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem parity_jump144 (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf 144 base (a) (b) (c) (scratch) reserve) =
      (cfgHalf 142 base (a) (b) (c) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, parity_row144, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem parity_drain_c (n : Nat) (base : RegisterMachine.Bank 9) (a b scratch : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf 140 base a b n scratch reserve) (2*n+1)
      (cfgHalf 142 base a b 0 scratch (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing reserve with
  | zero => simpa using WordEventSystem.Block.single graphSystem (parity_zero_c base a b 0 scratch reserve)
  | succ n ih =>
    have h1 := WordEventSystem.Block.single graphSystem (parity_dec_c base a b n scratch reserve)
    have h2 := WordEventSystem.Block.single graphSystem (parity_jump141 base a b n scratch (reserve ++ [0]))
    have h := (h1.trans graphSystem h2).trans graphSystem (ih (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem parity_restore_scratch (n : Nat) (base : RegisterMachine.Bank 9) (a b c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf 142 base a b c n reserve) (3*n+1)
      (cfgHalf 145 base a (b+n) c 0 (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing b reserve with
  | zero => simpa using WordEventSystem.Block.single graphSystem (parity_zero_scratch base a b c 0 reserve)
  | succ n ih =>
    have h1 := WordEventSystem.Block.single graphSystem (parity_dec_scratch base a b c n reserve)
    have h2 := WordEventSystem.Block.single graphSystem (parity_inc_b base a b c n (reserve ++ [0]))
    have h3 := WordEventSystem.Block.single graphSystem (parity_jump144 base a (b+1) c n (reserve ++ [0]))
    have h := ((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem (ih (b+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem parity_even (n : Nat) (base : RegisterMachine.Bank 9) (a : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf 133 base a (2*n) 0 0 reserve) (10*n+3)
      (cfgHalf 145 base a 0 0 0 (reserve ++ List.replicate (4*n) 0)) [] := by
  have h1 : graphSystem.Block (cfgHalf 133 base a (2*n) 0 0 reserve) (8*n)
      (cfgHalf 133 base a 0 n 0 (reserve ++ List.replicate (3*n) 0)) [] := by
    simpa using parity_scan_pairs n base a 0 0 reserve
  have h2 := WordEventSystem.Block.single graphSystem (parity_b_zero base a 0 n 0 (reserve ++ List.replicate (3*n) 0))
  have h3 := parity_drain_c n base a 0 0 (reserve ++ List.replicate (3*n) 0)
  have h4 := WordEventSystem.Block.single graphSystem (parity_zero_scratch base a 0 0 0
    ((reserve ++ List.replicate (3*n) 0) ++ List.replicate n 0))
  have h := ((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4
  have hr : (reserve ++ List.replicate (3*n) 0) ++ List.replicate n 0 = reserve ++ List.replicate (4*n) 0 := by
    have heq : 4*n = 3*n+n := by omega
    rw [heq, List.replicate_add, List.append_assoc]
  rw [hr] at h
  have ht : 8*n+1+(2*n+1)+1 = 10*n+3 := by omega
  simpa [ht] using h

theorem parity_odd (n : Nat) (base : RegisterMachine.Bank 9) (a : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf 133 base a (2*n+1) 0 0 reserve) (10*n+10)
      (cfgHalf 145 base a 1 0 0 (reserve ++ List.replicate (4*n+2) 0)) [] := by
  have h1 : graphSystem.Block (cfgHalf 133 base a (2*n+1) 0 0 reserve) (8*n)
      (cfgHalf 133 base a 1 n 0 (reserve ++ List.replicate (3*n) 0)) [] := by
    simpa using parity_scan_pairs n base a 1 0 reserve
  let r := reserve ++ List.replicate (3*n) 0
  have h2 := WordEventSystem.Block.single graphSystem (parity_b_dec base a 0 n 0 r)
  have h3 := WordEventSystem.Block.single graphSystem (parity_inc_scratch base a 0 n 0 (r ++ [0]))
  have h4 := WordEventSystem.Block.single graphSystem (parity_b_zero_second base a 0 n 1 (r ++ [0]))
  have h5 := WordEventSystem.Block.single graphSystem (parity_jump139 base a 0 n 1 (r ++ [0]))
  have h6 := WordEventSystem.Block.single graphSystem (parity_b_zero base a 0 n 1 (r ++ [0]))
  have h7 := parity_drain_c n base a 0 1 (r ++ [0])
  let t := (r ++ [0]) ++ List.replicate n 0
  have h8 := parity_restore_scratch 1 base a 0 0 t
  have h := ((((((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4).trans graphSystem h5).trans graphSystem h6).trans graphSystem h7).trans graphSystem h8
  have hr : t ++ [0] = reserve ++ List.replicate (4*n+2) 0 := by
    dsimp [t, r]
    change (((reserve ++ List.replicate (3*n) 0) ++ List.replicate 1 0) ++ List.replicate n 0) ++ List.replicate 1 0 = _
    have heq : 4*n+2 = 3*n+1+n+1 := by omega
    rw [heq]
    simp only [List.append_assoc, ← List.replicate_add]
  have ht : 8*n+1+1+1+1+1+(2*n+1)+(3*1+1) = 10*n+10 := by omega
  simp only [List.replicate_succ, List.replicate_zero] at h
  rw [hr] at h
  simpa [ht] using h

/-- Exact graph parity extraction on arbitrary input. -/
theorem parity_extract (b : Nat) (base : RegisterMachine.Bank 9) (a : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf 133 base a b 0 0 reserve) (10*(b/2)+3+7*(b%2))
      (cfgHalf 145 base a (b%2) 0 0 (reserve ++ List.replicate (2*b) 0)) [] := by
  have hm : b%2 = 0 ∨ b%2 = 1 := by omega
  rcases hm with hm | hm
  · have hb : b = 2*(b/2) := by omega
    have hr : 2*b = 4*(b/2) := by omega
    simp only [hm, Nat.mul_zero, Nat.add_zero, hr]
    simpa only [← hb] using parity_even (b/2) base a reserve
  · have hb : b = 2*(b/2)+1 := by omega
    have hr : 2*b = 4*(b/2)+2 := by omega
    simp only [hm, Nat.mul_one, hr]
    simpa only [← hb, show 3+7 = 10 by decide, Nat.add_assoc] using parity_odd (b/2) base a reserve

theorem shifted_parity_testBit (b n : Nat) :
    (b / 2^n) % 2 = if b.testBit n then 1 else 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hm : (b / 2^n) % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases h : (b / 2^n) % 2 = 1
  · simp [h]
  · have hz : (b / 2^n) % 2 = 0 := by omega
    simp [hz]

/-- Arbitrary prepared position and value produce the exact bit at row 145,
with finite positive progress, untouched registers and only zero padding. -/
theorem repeated_shift_bit (n b : Nat) (base : RegisterMachine.Bank 9) (reserve : List Nat) :
    ∃ duration padding, n+1 ≤ duration ∧
      graphSystem.Block (cfgHalf 119 base n b 0 0 reserve) duration
        (cfgHalf 145 base 0 (if b.testBit n then 1 else 0) 0 0
          (reserve ++ List.replicate padding 0)) [] := by
  obtain ⟨duration, padding, ht, h1⟩ := half_repeated_to_parity n b base reserve
  have h2 := parity_extract (b / 2^n) base 0 (reserve ++ List.replicate padding 0)
  have h := h1.trans graphSystem h2
  refine ⟨duration+(10*((b/2^n)/2)+3+7*((b/2^n)%2)), padding+2*(b/2^n), by omega, ?_⟩
  have hr : (reserve ++ List.replicate padding 0) ++ List.replicate (2*(b/2^n)) 0 =
      reserve ++ List.replicate (padding+2*(b/2^n)) 0 := by
    simp only [List.append_assoc, ← List.replicate_add]
  rw [hr, shifted_parity_testBit] at h
  rw [shifted_parity_testBit]
  simpa using h

/-- The complete budget-success block and bit extraction, under the existing
prepared-entry and successful-budget hypotheses. -/
theorem budget_success_then_bit (n remaining : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hc : base 8 = 0) (hcount : base 3 = remaining+n) :
    ∃ duration padding, n+1 ≤ duration ∧
      graphSystem.Block (cfgAS 103 base n 0 reserve) ((10*n+2)+duration)
        (cfgHalf 145 (bankBudget (bankAS base n 0) (base 3) (base 5+n) n 0)
          0 (if (base 7).testBit n then 1 else 0) 0 0
          (reserve ++ List.replicate (3*n+padding) 0)) [] := by
  have h1 := emitted_coordinate_budget_success n remaining base reserve hc hcount
  have hs : bankAS base n 0 0 = 0 := by simp [bankAS]
  rw [budget_exit_to_half (bankAS base n 0) (base 3) (base 5+n) n _ hs] at h1
  obtain ⟨duration, padding, ht, h2⟩ := repeated_shift_bit n (base 7)
    (bankBudget (bankAS base n 0) (base 3) (base 5+n) n 0)
    ((reserve ++ List.replicate (2*n) 0) ++ List.replicate n 0)
  have h := h1.trans graphSystem h2
  refine ⟨duration, padding, ht, ?_⟩
  have hr : ((reserve ++ List.replicate (2*n) 0) ++ List.replicate n 0) ++ List.replicate padding 0 =
      reserve ++ List.replicate (3*n+padding) 0 := by
    have heq : 3*n = 2*n+n := by omega
    rw [heq]
    simp only [List.append_assoc, ← List.replicate_add]
  rw [hr] at h
  simpa [bankAS] using h

/-- Physical lift at a graph entry explicitly reached by the selected
blank-start run; this does not establish such reachability. -/
theorem selected_repeated_shift_bit (i n b : Nat) (base : RegisterMachine.Bank 9) (reserve : List Nat)
    (h : graphSystem.run i = cfgHalf 119 base n b 0 0 reserve) :
    ∃ duration padding finish, n+1 ≤ duration ∧ Good finish ∧
      finish.graphState = cfgHalf 145 base 0 (if b.testBit n then 1 else 0) 0 0
        (reserve ++ List.replicate padding 0) ∧
      graphSystem.run (i+duration) = cfgHalf 145 base 0 (if b.testBit n then 1 else 0) 0 0
        (reserve ++ List.replicate padding 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run (graphRefinement.boundary (i+duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i+duration) := by
  obtain ⟨duration, padding, ht, block⟩ := repeated_shift_bit n b base reserve
  have hr : graphSystem.run (i+duration) = cfgHalf 145 base 0 (if b.testBit n then 1 else 0) 0 0
      (reserve ++ List.replicate padding 0) := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i+duration) = graphSystem.prefixWord i := by
    rw [WordEventSystem.prefix_add, h, block.output, List.append_nil]
  obtain ⟨finish, hg, hs, hconfig⟩ := graphRefinement.related (i+duration)
  refine ⟨duration, padding, finish, ht, hg, hs.trans hr, hr, hconfig, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

end PASoundness.M236.OccurrenceGraph
