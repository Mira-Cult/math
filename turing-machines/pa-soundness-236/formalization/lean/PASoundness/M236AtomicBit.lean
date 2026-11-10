import PASoundness.M236RepeatedShift
import PASoundness.M236AtomFirstLookup

/-! Register-level atomic bit extraction at the retained graph occurrences. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

structure AtomicBitRows (k : Nat) : Prop where
  row0 : sourceRows[k]? = some ("3.k.a.decnz", k+1, some (k+14))
  row1 : sourceRows[k+1]? = some ("3.k.b.decnz", k+2, some (k+8))
  row2 : sourceRows[k+2]? = some ("3.scratch.copy.inc", k+3, none)
  row3 : sourceRows[k+3]? = some ("3.k.b.decnz", k+4, some (k+7))
  row4 : sourceRows[k+4]? = some ("3.scratch.copy.decnz", k+5, some (k+6))
  row5 : sourceRows[k+5]? = some ("jump", k+4, none)
  row6 : sourceRows[k+6]? = some ("3.k.c.inc", k+7, none)
  row7 : sourceRows[k+7]? = some ("jump", k+1, none)
  row8 : sourceRows[k+8]? = some ("3.k.c.decnz", k+9, some (k+11))
  row9 : sourceRows[k+9]? = some ("3.k.b.inc", k+10, none)
  row10 : sourceRows[k+10]? = some ("jump", k+8, none)
  row11 : sourceRows[k+11]? = some ("3.scratch.copy.decnz", k+12, some (k+13))
  row12 : sourceRows[k+12]? = some ("jump", k+11, none)
  row13 : sourceRows[k+13]? = some ("jump", k, none)
  row14 : sourceRows[k+14]? = some ("3.k.b.decnz", k+15, some (k+21))
  row15 : sourceRows[k+15]? = some ("3.scratch.copy.inc", k+16, none)
  row16 : sourceRows[k+16]? = some ("3.k.b.decnz", k+17, some (k+20))
  row17 : sourceRows[k+17]? = some ("3.scratch.copy.decnz", k+18, some (k+19))
  row18 : sourceRows[k+18]? = some ("jump", k+17, none)
  row19 : sourceRows[k+19]? = some ("3.k.c.inc", k+20, none)
  row20 : sourceRows[k+20]? = some ("jump", k+14, none)
  row21 : sourceRows[k+21]? = some ("3.k.c.decnz", k+22, some (k+23))
  row22 : sourceRows[k+22]? = some ("jump", k+21, none)
  row23 : sourceRows[k+23]? = some ("3.scratch.copy.decnz", k+24, some (k+26))
  row24 : sourceRows[k+24]? = some ("3.k.b.inc", k+25, none)
  row25 : sourceRows[k+25]? = some ("jump", k+23, none)

theorem atomic_bit_rows_119 : AtomicBitRows 119 := by constructor <;> decide
theorem atomic_bit_rows_336 : AtomicBitRows 336 := by constructor <;> decide
theorem atomic_bit_rows_513 : AtomicBitRows 513 := by constructor <;> decide
theorem atomic_bit_rows_693 : AtomicBitRows 693 := by constructor <;> decide

theorem gbit_half_a_dec (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf k base (a+1) (b) (c) (scratch) reserve) =
      (cfgHalf (k+1) base (a) (b) (c) (scratch) (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row0, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem gbit_half_a_zero (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (_a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf k base (0) (b) (c) (scratch) reserve) =
      (cfgHalf (k+14) base (0) (b) (c) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row0, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem gbit_half_b_dec_120 (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+1) base (a) (b+1) (c) (scratch) reserve) =
      (cfgHalf (k+2) base (a) (b) (c) (scratch) (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row1, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem gbit_half_b_zero_120 (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a _b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+1) base (a) (0) (c) (scratch) reserve) =
      (cfgHalf (k+8) base (a) (0) (c) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row1, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem gbit_half_inc_scratch (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+2) base (a) (b) (c) (scratch) reserve) =
      (cfgHalf (k+3) base (a) (b) (c) (scratch+1) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row2, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem gbit_half_b_dec_122 (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+3) base (a) (b+1) (c) (scratch) reserve) =
      (cfgHalf (k+4) base (a) (b) (c) (scratch) (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row3, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem gbit_half_b_zero_122 (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a _b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+3) base (a) (0) (c) (scratch) reserve) =
      (cfgHalf (k+7) base (a) (0) (c) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row3, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem gbit_half_scratch_dec_123 (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+4) base (a) (b) (c) (scratch+1) reserve) =
      (cfgHalf (k+5) base (a) (b) (c) (scratch) (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row4, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem gbit_half_scratch_zero_123 (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b c _scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+4) base (a) (b) (c) (0) reserve) =
      (cfgHalf (k+6) base (a) (b) (c) (0) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row4, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem gbit_half_jump124 (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+5) base (a) (b) (c) (scratch) reserve) =
      (cfgHalf (k+4) base (a) (b) (c) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row5, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem gbit_half_inc_c (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+6) base (a) (b) (c) (scratch) reserve) =
      (cfgHalf (k+7) base (a) (b) (c+1) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row6, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem gbit_half_jump126 (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+7) base (a) (b) (c) (scratch) reserve) =
      (cfgHalf (k+1) base (a) (b) (c) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row7, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem gbit_half_c_dec (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+8) base (a) (b) (c+1) (scratch) reserve) =
      (cfgHalf (k+9) base (a) (b) (c) (scratch) (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row8, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem gbit_half_c_zero (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b _c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+8) base (a) (b) (0) (scratch) reserve) =
      (cfgHalf (k+11) base (a) (b) (0) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row8, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem gbit_half_inc_b (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+9) base (a) (b) (c) (scratch) reserve) =
      (cfgHalf (k+10) base (a) (b+1) (c) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row9, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem gbit_half_jump129 (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+10) base (a) (b) (c) (scratch) reserve) =
      (cfgHalf (k+8) base (a) (b) (c) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row10, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem gbit_half_scratch_dec_130 (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+11) base (a) (b) (c) (scratch+1) reserve) =
      (cfgHalf (k+12) base (a) (b) (c) (scratch) (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row11, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem gbit_half_scratch_zero_130 (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b c _scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+11) base (a) (b) (c) (0) reserve) =
      (cfgHalf (k+13) base (a) (b) (c) (0) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row11, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem gbit_half_jump131 (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+12) base (a) (b) (c) (scratch) reserve) =
      (cfgHalf (k+11) base (a) (b) (c) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row12, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem gbit_half_jump132 (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+13) base (a) (b) (c) (scratch) reserve) =
      (cfgHalf k base (a) (b) (c) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row13, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]


/-- Two `b` units produce one `c` unit, clear scratch and add three
zero reserve blocks. -/
theorem gbit_half_pair_cycle (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf (k+1) base a (b+2) c 0 reserve) 8
      (cfgHalf (k+1) base a b (c+1) 0 (reserve ++ [0,0,0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (gbit_half_b_dec_120 k rows base a (b+1) c 0 reserve)
  have h2 := WordEventSystem.Block.single graphSystem (gbit_half_inc_scratch k rows base a (b+1) c 0 (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (gbit_half_b_dec_122 k rows base a b c 1 (reserve ++ [0]))
  have h4 := WordEventSystem.Block.single graphSystem (gbit_half_scratch_dec_123 k rows base a b c 0 ((reserve ++ [0]) ++ [0]))
  have h5 := WordEventSystem.Block.single graphSystem (gbit_half_jump124 k rows base a b c 0 (((reserve ++ [0]) ++ [0]) ++ [0]))
  have h6 := WordEventSystem.Block.single graphSystem (gbit_half_scratch_zero_123 k rows base a b c 0 (((reserve ++ [0]) ++ [0]) ++ [0]))
  have h7 := WordEventSystem.Block.single graphSystem (gbit_half_inc_c k rows base a b c 0 (((reserve ++ [0]) ++ [0]) ++ [0]))
  have h8 := WordEventSystem.Block.single graphSystem (gbit_half_jump126 k rows base a b (c+1) 0 (((reserve ++ [0]) ++ [0]) ++ [0]))
  simpa [List.append_assoc] using ((((((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4).trans graphSystem h5).trans graphSystem h6).trans graphSystem h7).trans graphSystem h8

theorem gbit_half_scan_pairs (k : Nat) (rows : AtomicBitRows k) (n : Nat) (base : RegisterMachine.Bank 9) (a r c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf (k+1) base a (2*n+r) c 0 reserve) (8*n)
      (cfgHalf (k+1) base a r (c+n) 0 (reserve ++ List.replicate (3*n) 0)) [] := by
  induction n generalizing c reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgHalf (k+1) base a r c 0 reserve)
  | succ n ih =>
    have h := (gbit_half_pair_cycle k rows base a (2*n+r) c reserve).trans graphSystem (ih (c+1) (reserve ++ [0,0,0]))
    have hr : (reserve ++ [0,0,0]) ++ List.replicate (3*n) 0 =
        reserve ++ List.replicate (3*(n+1)) 0 := by
      have hn : 3*(n+1) = 3+3*n := by omega
      rw [hn, List.replicate_add]
      simp [List.replicate_succ, List.append_assoc]
    rw [hr] at h
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem gbit_half_restore_all (k : Nat) (rows : AtomicBitRows k) (n : Nat) (base : RegisterMachine.Bank 9) (a b scratch : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf (k+8) base a b n scratch reserve) (3*n)
      (cfgHalf (k+8) base a (b+n) 0 scratch (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing b reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgHalf (k+8) base a b 0 scratch reserve)
  | succ n ih =>
    have h1 := WordEventSystem.Block.single graphSystem (gbit_half_c_dec k rows base a b n scratch reserve)
    have h2 := WordEventSystem.Block.single graphSystem (gbit_half_inc_b k rows base a b n scratch (reserve ++ [0]))
    have h3 := WordEventSystem.Block.single graphSystem (gbit_half_jump129 k rows base a (b+1) n scratch (reserve ++ [0]))
    have h := ((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem (ih (b+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem gbit_half_clear_scratch (k : Nat) (rows : AtomicBitRows k) (n : Nat) (base : RegisterMachine.Bank 9) (a b c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf (k+11) base a b c n reserve) (2*n+1)
      (cfgHalf (k+13) base a b c 0 (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing reserve with
  | zero => simpa using WordEventSystem.Block.single graphSystem (gbit_half_scratch_zero_130 k rows base a b c 0 reserve)
  | succ n ih =>
    have h1 := WordEventSystem.Block.single graphSystem (gbit_half_scratch_dec_130 k rows base a b c n reserve)
    have h2 := WordEventSystem.Block.single graphSystem (gbit_half_jump131 k rows base a b c n (reserve ++ [0]))
    have h := (h1.trans graphSystem h2).trans graphSystem (ih (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

/-- For an even input, a half pass takes exactly `11*n+4` graph steps,
appends `4*n` zero reserve blocks, and emits nothing. -/
theorem gbit_half_pass_even (k : Nat) (rows : AtomicBitRows k) (n : Nat) (base : RegisterMachine.Bank 9) (a : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf (k+1) base a (2*n) 0 0 reserve) (11*n+4)
      (cfgHalf k base a n 0 0 (reserve ++ List.replicate (4*n) 0)) [] := by
  have h1 : graphSystem.Block (cfgHalf (k+1) base a (2*n) 0 0 reserve) (8*n)
      (cfgHalf (k+1) base a 0 n 0 (reserve ++ List.replicate (3*n) 0)) [] := by
    simpa using gbit_half_scan_pairs k rows n base a 0 0 reserve
  have h2 := WordEventSystem.Block.single graphSystem (gbit_half_b_zero_120 k rows base a 0 n 0 (reserve ++ List.replicate (3*n) 0))
  have h3 := gbit_half_restore_all k rows n base a 0 0 (reserve ++ List.replicate (3*n) 0)
  simp only [Nat.zero_add] at h3
  have h4 := WordEventSystem.Block.single graphSystem (gbit_half_c_zero k rows base a n 0 0 ((reserve ++ List.replicate (3*n) 0) ++ List.replicate n 0))
  have h5 := WordEventSystem.Block.single graphSystem (gbit_half_scratch_zero_130 k rows base a n 0 0 ((reserve ++ List.replicate (3*n) 0) ++ List.replicate n 0))
  have h6 := WordEventSystem.Block.single graphSystem (gbit_half_jump132 k rows base a n 0 0 ((reserve ++ List.replicate (3*n) 0) ++ List.replicate n 0))
  have h := ((((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4).trans graphSystem h5).trans graphSystem h6
  have hr : (reserve ++ List.replicate (3*n) 0) ++ List.replicate n 0 = reserve ++ List.replicate (4*n) 0 := by
    have heq : 4*n = 3*n+n := by omega
    rw [heq, List.replicate_add, List.append_assoc]
  rw [hr] at h
  have ht : 8*n+1+3*n+1+1+1 = 11*n+4 := by omega
  simpa [ht] using h

/-- The odd case clears the remainder after the quotient is restored. -/
theorem gbit_half_pass_odd (k : Nat) (rows : AtomicBitRows k) (n : Nat) (base : RegisterMachine.Bank 9) (a : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf (k+1) base a (2*n+1) 0 0 reserve) (11*n+10)
      (cfgHalf k base a n 0 0 (reserve ++ List.replicate (4*n+2) 0)) [] := by
  have h1 : graphSystem.Block (cfgHalf (k+1) base a (2*n+1) 0 0 reserve) (8*n)
      (cfgHalf (k+1) base a 1 n 0 (reserve ++ List.replicate (3*n) 0)) [] := by
    simpa using gbit_half_scan_pairs k rows n base a 1 0 reserve
  let r := reserve ++ List.replicate (3*n) 0
  have h2 := WordEventSystem.Block.single graphSystem (gbit_half_b_dec_120 k rows base a 0 n 0 r)
  have h3 := WordEventSystem.Block.single graphSystem (gbit_half_inc_scratch k rows base a 0 n 0 (r ++ [0]))
  have h4 := WordEventSystem.Block.single graphSystem (gbit_half_b_zero_122 k rows base a 0 n 1 (r ++ [0]))
  have h5 := WordEventSystem.Block.single graphSystem (gbit_half_jump126 k rows base a 0 n 1 (r ++ [0]))
  have h6 := WordEventSystem.Block.single graphSystem (gbit_half_b_zero_120 k rows base a 0 n 1 (r ++ [0]))
  have h7 := gbit_half_restore_all k rows n base a 0 1 (r ++ [0])
  simp only [Nat.zero_add] at h7
  let s := (r ++ [0]) ++ List.replicate n 0
  have h8 := WordEventSystem.Block.single graphSystem (gbit_half_c_zero k rows base a n 0 1 s)
  have h9 := gbit_half_clear_scratch k rows 1 base a n 0 s
  have h10 := WordEventSystem.Block.single graphSystem (gbit_half_jump132 k rows base a n 0 0 (s ++ [0]))
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
theorem gbit_half_pass (k : Nat) (rows : AtomicBitRows k) (b : Nat) (base : RegisterMachine.Bank 9) (a : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf (k+1) base a b 0 0 reserve) (11*(b/2)+4+6*(b%2))
      (cfgHalf k base a (b/2) 0 0 (reserve ++ List.replicate (2*b) 0)) [] := by
  have hm : b%2 = 0 ∨ b%2 = 1 := by omega
  rcases hm with hm | hm
  · have hb : b = 2*(b/2) := by omega
    have hr : 2*b = 4*(b/2) := by omega
    simp only [hm, Nat.mul_zero, Nat.add_zero, hr]
    simpa only [← hb] using gbit_half_pass_even k rows (b/2) base a reserve
  · have hb : b = 2*(b/2)+1 := by omega
    have hr : 2*b = 4*(b/2)+2 := by omega
    simp only [hm, Nat.mul_one, hr]
    simpa only [← hb, show 4+6 = 10 by decide, Nat.add_assoc] using gbit_half_pass_odd k rows (b/2) base a reserve

/-- A positive `a` at entry `k` performs one exact silent right shift of `b`.
The prepared work registers `c` and scratch are zero. -/
theorem gbit_half_step (k : Nat) (rows : AtomicBitRows k) (a b : Nat) (base : RegisterMachine.Bank 9) (reserve : List Nat) :
    graphSystem.Block (cfgHalf k base (a+1) b 0 0 reserve) (11*(b/2)+5+6*(b%2))
      (cfgHalf k base a (b/2) 0 0 (reserve ++ List.replicate (2*b+1) 0)) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (gbit_half_a_dec k rows base a b 0 0 reserve)
  have h2 := gbit_half_pass k rows b base a (reserve ++ [0])
  have h := h1.trans graphSystem h2
  have hr : (reserve ++ [0]) ++ List.replicate (2*b) 0 =
      reserve ++ List.replicate (2*b+1) 0 := by
    have heq : 2*b+1 = 1+2*b := by omega
    rw [heq, List.replicate_add]
    simp [List.append_assoc]
  rw [hr] at h
  have ht : 1+(11*(b/2)+4+6*(b%2)) = 11*(b/2)+5+6*(b%2) := by omega
  simpa [ht] using h

theorem gbit_half_repeated (k : Nat) (rows : AtomicBitRows k) (n b : Nat) (base : RegisterMachine.Bank 9) (reserve : List Nat) :
    ∃ duration padding, n ≤ duration ∧
      graphSystem.Block (cfgHalf k base n b 0 0 reserve) duration
        (cfgHalf k base 0 (b / 2^n) 0 0 (reserve ++ List.replicate padding 0)) [] := by
  induction n generalizing b reserve with
  | zero =>
    refine ⟨0, 0, by omega, ?_⟩
    simpa using WordEventSystem.Block.refl graphSystem (cfgHalf k base 0 b 0 0 reserve)
  | succ n ih =>
    have h1 := gbit_half_step k rows n b base reserve
    obtain ⟨duration, padding, ht, h2⟩ := ih (b/2) (reserve ++ List.replicate (2*b+1) 0)
    have h := h1.trans graphSystem h2
    refine ⟨(11*(b/2)+5+6*(b%2))+duration, (2*b+1)+padding, by omega, ?_⟩
    have hr : (reserve ++ List.replicate (2*b+1) 0) ++ List.replicate padding 0 =
        reserve ++ List.replicate ((2*b+1)+padding) 0 := by
      simp only [List.append_assoc, ← List.replicate_add]
    rw [hr] at h
    simpa [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm] using h

/-- Once all shifts finish, the zero branch enters the parity extractor. -/
theorem gbit_half_repeated_to_parity (k : Nat) (rows : AtomicBitRows k) (n b : Nat) (base : RegisterMachine.Bank 9) (reserve : List Nat) :
    ∃ duration padding, n+1 ≤ duration ∧
      graphSystem.Block (cfgHalf k base n b 0 0 reserve) duration
        (cfgHalf (k+14) base 0 (b / 2^n) 0 0 (reserve ++ List.replicate padding 0)) [] := by
  obtain ⟨duration, padding, ht, h⟩ := gbit_half_repeated k rows n b base reserve
  have hzero := WordEventSystem.Block.single graphSystem
    (gbit_half_a_zero k rows base 0 (b / 2^n) 0 0 (reserve ++ List.replicate padding 0))
  refine ⟨duration+1, padding, by omega, ?_⟩
  simpa using h.trans graphSystem hzero


theorem gbit_parity_b_dec (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+14) base (a) (b+1) (c) (scratch) reserve) =
      (cfgHalf (k+15) base (a) (b) (c) (scratch) (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row14, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])


theorem gbit_parity_b_zero (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a _b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+14) base (a) (0) (c) (scratch) reserve) =
      (cfgHalf (k+21) base (a) (0) (c) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row14, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]


theorem gbit_parity_inc_scratch (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+15) base (a) (b) (c) (scratch) reserve) =
      (cfgHalf (k+16) base (a) (b) (c) (scratch+1) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row15, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])


theorem gbit_parity_b_dec_second (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+16) base (a) (b+1) (c) (scratch) reserve) =
      (cfgHalf (k+17) base (a) (b) (c) (scratch) (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row16, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])


theorem gbit_parity_b_zero_second (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a _b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+16) base (a) (0) (c) (scratch) reserve) =
      (cfgHalf (k+20) base (a) (0) (c) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row16, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]


theorem gbit_parity_scratch_dec (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+17) base (a) (b) (c) (scratch+1) reserve) =
      (cfgHalf (k+18) base (a) (b) (c) (scratch) (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row17, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])


theorem gbit_parity_scratch_zero (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b c _scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+17) base (a) (b) (c) (0) reserve) =
      (cfgHalf (k+19) base (a) (b) (c) (0) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row17, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]


theorem gbit_parity_jump137 (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+18) base (a) (b) (c) (scratch) reserve) =
      (cfgHalf (k+17) base (a) (b) (c) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row18, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]


theorem gbit_parity_inc_c (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+19) base (a) (b) (c) (scratch) reserve) =
      (cfgHalf (k+20) base (a) (b) (c+1) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row19, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])


theorem gbit_parity_jump139 (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+20) base (a) (b) (c) (scratch) reserve) =
      (cfgHalf (k+14) base (a) (b) (c) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row20, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]


theorem gbit_parity_pair_cycle (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf (k+14) base a (b+2) c 0 reserve) 8
      (cfgHalf (k+14) base a b (c+1) 0 (reserve ++ [0,0,0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (gbit_parity_b_dec k rows base a (b+1) c 0 reserve)
  have h2 := WordEventSystem.Block.single graphSystem (gbit_parity_inc_scratch k rows base a (b+1) c 0 (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (gbit_parity_b_dec_second k rows base a b c 1 (reserve ++ [0]))
  have h4 := WordEventSystem.Block.single graphSystem (gbit_parity_scratch_dec k rows base a b c 0 ((reserve ++ [0]) ++ [0]))
  have h5 := WordEventSystem.Block.single graphSystem (gbit_parity_jump137 k rows base a b c 0 (((reserve ++ [0]) ++ [0]) ++ [0]))
  have h6 := WordEventSystem.Block.single graphSystem (gbit_parity_scratch_zero k rows base a b c 0 (((reserve ++ [0]) ++ [0]) ++ [0]))
  have h7 := WordEventSystem.Block.single graphSystem (gbit_parity_inc_c k rows base a b c 0 (((reserve ++ [0]) ++ [0]) ++ [0]))
  have h8 := WordEventSystem.Block.single graphSystem (gbit_parity_jump139 k rows base a b (c+1) 0 (((reserve ++ [0]) ++ [0]) ++ [0]))
  simpa [List.append_assoc] using ((((((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4).trans graphSystem h5).trans graphSystem h6).trans graphSystem h7).trans graphSystem h8


theorem gbit_parity_scan_pairs (k : Nat) (rows : AtomicBitRows k) (n : Nat) (base : RegisterMachine.Bank 9) (a r c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf (k+14) base a (2*n+r) c 0 reserve) (8*n)
      (cfgHalf (k+14) base a r (c+n) 0 (reserve ++ List.replicate (3*n) 0)) [] := by
  induction n generalizing c reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgHalf (k+14) base a r c 0 reserve)
  | succ n ih =>
    have h := (gbit_parity_pair_cycle k rows base a (2*n+r) c reserve).trans graphSystem (ih (c+1) (reserve ++ [0,0,0]))
    have hr : (reserve ++ [0,0,0]) ++ List.replicate (3*n) 0 =
        reserve ++ List.replicate (3*(n+1)) 0 := by
      have hn : 3*(n+1) = 3+3*n := by omega
      rw [hn, List.replicate_add]
      simp [List.replicate_succ, List.append_assoc]
    rw [hr] at h
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h


theorem gbit_parity_dec_c (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+21) base (a) (b) (c+1) (scratch) reserve) =
      (cfgHalf (k+22) base (a) (b) (c) (scratch) (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row21, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem gbit_parity_zero_c (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b _c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+21) base (a) (b) (0) (scratch) reserve) =
      (cfgHalf (k+23) base (a) (b) (0) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row21, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem gbit_parity_jump141 (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+22) base (a) (b) (c) (scratch) reserve) =
      (cfgHalf (k+21) base (a) (b) (c) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row22, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem gbit_parity_dec_scratch (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+23) base (a) (b) (c) (scratch+1) reserve) =
      (cfgHalf (k+24) base (a) (b) (c) (scratch) (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row23, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem gbit_parity_zero_scratch (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b c _scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+23) base (a) (b) (c) (0) reserve) =
      (cfgHalf (k+26) base (a) (b) (c) (0) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row23, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem gbit_parity_inc_b (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+24) base (a) (b) (c) (scratch) reserve) =
      (cfgHalf (k+25) base (a) (b+1) (c) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row24, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem gbit_parity_jump144 (k : Nat) (rows : AtomicBitRows k) (base : RegisterMachine.Bank 9) (a b c scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+25) base (a) (b) (c) (scratch) reserve) =
      (cfgHalf (k+23) base (a) (b) (c) (scratch) reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.row25, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem gbit_parity_drain_c (k : Nat) (rows : AtomicBitRows k) (n : Nat) (base : RegisterMachine.Bank 9) (a b scratch : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf (k+21) base a b n scratch reserve) (2*n+1)
      (cfgHalf (k+23) base a b 0 scratch (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing reserve with
  | zero => simpa using WordEventSystem.Block.single graphSystem (gbit_parity_zero_c k rows base a b 0 scratch reserve)
  | succ n ih =>
    have h1 := WordEventSystem.Block.single graphSystem (gbit_parity_dec_c k rows base a b n scratch reserve)
    have h2 := WordEventSystem.Block.single graphSystem (gbit_parity_jump141 k rows base a b n scratch (reserve ++ [0]))
    have h := (h1.trans graphSystem h2).trans graphSystem (ih (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem gbit_parity_restore_scratch (k : Nat) (rows : AtomicBitRows k) (n : Nat) (base : RegisterMachine.Bank 9) (a b c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf (k+23) base a b c n reserve) (3*n+1)
      (cfgHalf (k+26) base a (b+n) c 0 (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing b reserve with
  | zero => simpa using WordEventSystem.Block.single graphSystem (gbit_parity_zero_scratch k rows base a b c 0 reserve)
  | succ n ih =>
    have h1 := WordEventSystem.Block.single graphSystem (gbit_parity_dec_scratch k rows base a b c n reserve)
    have h2 := WordEventSystem.Block.single graphSystem (gbit_parity_inc_b k rows base a b c n (reserve ++ [0]))
    have h3 := WordEventSystem.Block.single graphSystem (gbit_parity_jump144 k rows base a (b+1) c n (reserve ++ [0]))
    have h := ((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem (ih (b+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem gbit_parity_even (k : Nat) (rows : AtomicBitRows k) (n : Nat) (base : RegisterMachine.Bank 9) (a : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf (k+14) base a (2*n) 0 0 reserve) (10*n+3)
      (cfgHalf (k+26) base a 0 0 0 (reserve ++ List.replicate (4*n) 0)) [] := by
  have h1 : graphSystem.Block (cfgHalf (k+14) base a (2*n) 0 0 reserve) (8*n)
      (cfgHalf (k+14) base a 0 n 0 (reserve ++ List.replicate (3*n) 0)) [] := by
    simpa using gbit_parity_scan_pairs k rows n base a 0 0 reserve
  have h2 := WordEventSystem.Block.single graphSystem (gbit_parity_b_zero k rows base a 0 n 0 (reserve ++ List.replicate (3*n) 0))
  have h3 := gbit_parity_drain_c k rows n base a 0 0 (reserve ++ List.replicate (3*n) 0)
  have h4 := WordEventSystem.Block.single graphSystem (gbit_parity_zero_scratch k rows base a 0 0 0
    ((reserve ++ List.replicate (3*n) 0) ++ List.replicate n 0))
  have h := ((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4
  have hr : (reserve ++ List.replicate (3*n) 0) ++ List.replicate n 0 = reserve ++ List.replicate (4*n) 0 := by
    have heq : 4*n = 3*n+n := by omega
    rw [heq, List.replicate_add, List.append_assoc]
  rw [hr] at h
  have ht : 8*n+1+(2*n+1)+1 = 10*n+3 := by omega
  simpa [ht] using h

theorem gbit_parity_odd (k : Nat) (rows : AtomicBitRows k) (n : Nat) (base : RegisterMachine.Bank 9) (a : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf (k+14) base a (2*n+1) 0 0 reserve) (10*n+10)
      (cfgHalf (k+26) base a 1 0 0 (reserve ++ List.replicate (4*n+2) 0)) [] := by
  have h1 : graphSystem.Block (cfgHalf (k+14) base a (2*n+1) 0 0 reserve) (8*n)
      (cfgHalf (k+14) base a 1 n 0 (reserve ++ List.replicate (3*n) 0)) [] := by
    simpa using gbit_parity_scan_pairs k rows n base a 1 0 reserve
  let r := reserve ++ List.replicate (3*n) 0
  have h2 := WordEventSystem.Block.single graphSystem (gbit_parity_b_dec k rows base a 0 n 0 r)
  have h3 := WordEventSystem.Block.single graphSystem (gbit_parity_inc_scratch k rows base a 0 n 0 (r ++ [0]))
  have h4 := WordEventSystem.Block.single graphSystem (gbit_parity_b_zero_second k rows base a 0 n 1 (r ++ [0]))
  have h5 := WordEventSystem.Block.single graphSystem (gbit_parity_jump139 k rows base a 0 n 1 (r ++ [0]))
  have h6 := WordEventSystem.Block.single graphSystem (gbit_parity_b_zero k rows base a 0 n 1 (r ++ [0]))
  have h7 := gbit_parity_drain_c k rows n base a 0 1 (r ++ [0])
  let t := (r ++ [0]) ++ List.replicate n 0
  have h8 := gbit_parity_restore_scratch k rows 1 base a 0 0 t
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
theorem gbit_parity_extract (k : Nat) (rows : AtomicBitRows k) (b : Nat) (base : RegisterMachine.Bank 9) (a : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf (k+14) base a b 0 0 reserve) (10*(b/2)+3+7*(b%2))
      (cfgHalf (k+26) base a (b%2) 0 0 (reserve ++ List.replicate (2*b) 0)) [] := by
  have hm : b%2 = 0 ∨ b%2 = 1 := by omega
  rcases hm with hm | hm
  · have hb : b = 2*(b/2) := by omega
    have hr : 2*b = 4*(b/2) := by omega
    simp only [hm, Nat.mul_zero, Nat.add_zero, hr]
    simpa only [← hb] using gbit_parity_even k rows (b/2) base a reserve
  · have hb : b = 2*(b/2)+1 := by omega
    have hr : 2*b = 4*(b/2)+2 := by omega
    simp only [hm, Nat.mul_one, hr]
    simpa only [← hb, show 3+7 = 10 by decide, Nat.add_assoc] using gbit_parity_odd k rows (b/2) base a reserve

/-- Arbitrary prepared position and value produce the exact bit at `k+26`,
with finite positive progress, untouched registers and only zero padding. -/
theorem gbit_repeated_shift_bit (k : Nat) (rows : AtomicBitRows k) (n b : Nat) (base : RegisterMachine.Bank 9) (reserve : List Nat) :
    ∃ duration padding, n+1 ≤ duration ∧
      graphSystem.Block (cfgHalf k base n b 0 0 reserve) duration
        (cfgHalf (k+26) base 0 (if b.testBit n then 1 else 0) 0 0
          (reserve ++ List.replicate padding 0)) [] := by
  obtain ⟨duration, padding, ht, h1⟩ := gbit_half_repeated_to_parity k rows n b base reserve
  have h2 := gbit_parity_extract k rows (b / 2^n) base 0 (reserve ++ List.replicate padding 0)
  have h := h1.trans graphSystem h2
  refine ⟨duration+(10*((b/2^n)/2)+3+7*((b/2^n)%2)), padding+2*(b/2^n), by omega, ?_⟩
  have hr : (reserve ++ List.replicate padding 0) ++ List.replicate (2*(b/2^n)) 0 =
      reserve ++ List.replicate (padding+2*(b/2^n)) 0 := by
    simp only [List.append_assoc, ← List.replicate_add]
  rw [hr, shifted_parity_testBit] at h
  rw [shifted_parity_testBit]
  simpa using h


/-- Prepared strict-atom operands followed by the checked bit routine. The
output is the natural encoding of `encodedAtom`; sign handling is separate. -/
theorem atomic_operands_to_bit (payload encoded k : Nat)
    (first : AtomFirstLookupRows k) (second : AtomSecondLookupRows (k+29))
    (bits : AtomicBitRows (k+66)) (base : RegisterMachine.Bank 9) (reserve : List Nat) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block
        (cfgAtom k base (Cantor.unpair payload).2 encoded (Cantor.unpair payload).1 0 0 0 reserve) duration
        (cfgAtom (k+92) base 0 0 0 (if M236Game.encodedAtom payload encoded then 1 else 0) 0 0
          (reserve ++ List.replicate padding 0)) [] := by
  obtain ⟨firstDuration, firstPadding, hf, h1⟩ := atom_lookup_operands
    (Cantor.unpair payload).1 (Cantor.unpair payload).2 encoded k first second base reserve
  obtain ⟨duration, padding, ht, h2⟩ := gbit_repeated_shift_bit (k+66) bits
    (M236Game.lookup encoded (Cantor.unpair payload).1)
    (M236Game.lookup encoded ((Cantor.unpair payload).1 + (Cantor.unpair payload).2 + 1))
    (RegisterMachine.write (RegisterMachine.write base 4 0) 5 0) (reserve ++ List.replicate firstPadding 0)
  change graphSystem.Block
    (cfgAtom (k+66) base 0 0 (M236Game.lookup encoded (Cantor.unpair payload).1)
      (M236Game.lookup encoded ((Cantor.unpair payload).1 + (Cantor.unpair payload).2 + 1)) 0 0
      (reserve ++ List.replicate firstPadding 0)) duration
    (cfgAtom (k+92) base 0 0 0
      (if (M236Game.lookup encoded ((Cantor.unpair payload).1 + (Cantor.unpair payload).2 + 1)).testBit
        (M236Game.lookup encoded (Cantor.unpair payload).1) then 1 else 0) 0 0
      ((reserve ++ List.replicate firstPadding 0) ++ List.replicate padding 0)) [] at h2
  rw [atom_lookup_operand_meaning] at h2
  have h := h1.trans graphSystem h2
  refine ⟨firstDuration+duration, firstPadding+padding, by omega, ?_⟩
  have hr : (reserve ++ List.replicate firstPadding 0) ++ List.replicate padding 0 =
      reserve ++ List.replicate (firstPadding+padding) 0 := by
    simp only [List.replicate_add, List.append_assoc]
  simp only [List.nil_append] at h
  rw [hr] at h
  exact h

structure AtomicStoreRows (k : Nat) : Prop where
  decB : sourceRows[k]? = some ("3.k.b.decnz", k+1, some (k+3))
  incTop : sourceRows[k+1]? = some ("3.k.top.inc", k+2, none)
  loop : sourceRows[k+2]? = some ("jump", k, none)
  finish : sourceRows[k+3]? = some ("jump", 724, none)

theorem atomic_store_rows_362 : AtomicStoreRows 362 := by constructor <;> decide
theorem atomic_store_rows_542 : AtomicStoreRows 542 := by constructor <;> decide
theorem atomic_store_rows_719 : AtomicStoreRows 719 := by constructor <;> decide

structure AtomicToggleRows (k : Nat) : Prop where
  decB : sourceRows[k]? = some ("3.k.b.decnz", k+1, some (k+2))
  jump : sourceRows[k+1]? = some ("jump", k+3, none)
  incB : sourceRows[k+2]? = some ("3.k.b.inc", k+3, none)

theorem atomic_toggle_rows_539 : AtomicToggleRows 539 := by constructor <;> decide

theorem atomic_store_dec (k : Nat) (rows : AtomicStoreRows k) (base : RegisterMachine.Bank 9)
    (top env a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAtom k base top env a (b+1) c s reserve) =
      (cfgAtom (k+1) base top env a b c s (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgAtom, cfgEnv, cfgHalf, rows.decB, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem atomic_store_zero (k : Nat) (rows : AtomicStoreRows k) (base : RegisterMachine.Bank 9)
    (top env a c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAtom k base top env a 0 c s reserve) =
      (cfgAtom (k+3) base top env a 0 c s reserve, []) := by
  simp [graphSystem, graphNext, cfgAtom, cfgEnv, cfgHalf, rows.decB, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem atomic_store_inc (k : Nat) (rows : AtomicStoreRows k) (base : RegisterMachine.Bank 9)
    (top env a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAtom (k+1) base top env a b c s reserve) =
      (cfgAtom (k+2) base (top+1) env a b c s reserve, []) := by
  simp [graphSystem, graphNext, cfgAtom, cfgEnv, cfgHalf, rows.incTop, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem atomic_store_jump (k : Nat) (rows : AtomicStoreRows k) (base : RegisterMachine.Bank 9)
    (top env a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAtom (k+2) base top env a b c s reserve) = (cfgAtom k base top env a b c s reserve, []) := by
  simp [graphSystem, graphNext, cfgAtom, cfgEnv, cfgHalf, rows.loop, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

theorem atomic_store_finish (k : Nat) (rows : AtomicStoreRows k) (base : RegisterMachine.Bank 9)
    (top env a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAtom (k+3) base top env a b c s reserve) = (cfgAtom 724 base top env a b c s reserve, []) := by
  simp [graphSystem, graphNext, cfgAtom, cfgEnv, cfgHalf, rows.finish, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

theorem atomic_store_bool (k : Nat) (rows : AtomicStoreRows k) (base : RegisterMachine.Bank 9)
    (bit : Bool) (reserve : List Nat) :
    graphSystem.Block (cfgAtom k base 0 0 0 (if bit then 1 else 0) 0 0 reserve)
      (if bit then 5 else 2)
      (cfgAtom 724 base (if bit then 1 else 0) 0 0 0 0 0
        (reserve ++ if bit then [0] else [])) [] := by
  cases bit with
  | false =>
    have h1 := WordEventSystem.Block.single graphSystem (atomic_store_zero k rows base 0 0 0 0 0 reserve)
    have h2 := WordEventSystem.Block.single graphSystem (atomic_store_finish k rows base 0 0 0 0 0 0 reserve)
    simpa using h1.trans graphSystem h2
  | true =>
    have h1 := WordEventSystem.Block.single graphSystem (atomic_store_dec k rows base 0 0 0 0 0 0 reserve)
    have h2 := WordEventSystem.Block.single graphSystem (atomic_store_inc k rows base 0 0 0 0 0 0 (reserve ++ [0]))
    have h3 := WordEventSystem.Block.single graphSystem (atomic_store_jump k rows base 1 0 0 0 0 0 (reserve ++ [0]))
    have h4 := WordEventSystem.Block.single graphSystem (atomic_store_zero k rows base 1 0 0 0 0 (reserve ++ [0]))
    have h5 := WordEventSystem.Block.single graphSystem (atomic_store_finish k rows base 1 0 0 0 0 0 (reserve ++ [0]))
    simpa using ((((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4).trans graphSystem h5)

theorem atomic_toggle_dec (k : Nat) (rows : AtomicToggleRows k) (base : RegisterMachine.Bank 9)
    (top env a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAtom k base top env a (b+1) c s reserve) =
      (cfgAtom (k+1) base top env a b c s (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgAtom, cfgEnv, cfgHalf, rows.decB, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem atomic_toggle_zero (k : Nat) (rows : AtomicToggleRows k) (base : RegisterMachine.Bank 9)
    (top env a c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAtom k base top env a 0 c s reserve) =
      (cfgAtom (k+2) base top env a 0 c s reserve, []) := by
  simp [graphSystem, graphNext, cfgAtom, cfgEnv, cfgHalf, rows.decB, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem atomic_toggle_jump (k : Nat) (rows : AtomicToggleRows k) (base : RegisterMachine.Bank 9)
    (top env a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAtom (k+1) base top env a b c s reserve) =
      (cfgAtom (k+3) base top env a b c s reserve, []) := by
  simp [graphSystem, graphNext, cfgAtom, cfgEnv, cfgHalf, rows.jump, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

theorem atomic_toggle_inc (k : Nat) (rows : AtomicToggleRows k) (base : RegisterMachine.Bank 9)
    (top env a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAtom (k+2) base top env a b c s reserve) =
      (cfgAtom (k+3) base top env a (b+1) c s reserve, []) := by
  simp [graphSystem, graphNext, cfgAtom, cfgEnv, cfgHalf, rows.incB, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem atomic_toggle_bool (k : Nat) (rows : AtomicToggleRows k) (base : RegisterMachine.Bank 9)
    (bit : Bool) (reserve : List Nat) :
    graphSystem.Block (cfgAtom k base 0 0 0 (if bit then 1 else 0) 0 0 reserve) 2
      (cfgAtom (k+3) base 0 0 0 (if !bit then 1 else 0) 0 0
        (reserve ++ if bit then [0] else [])) [] := by
  cases bit with
  | false =>
    have h1 := WordEventSystem.Block.single graphSystem (atomic_toggle_zero k rows base 0 0 0 0 0 reserve)
    have h2 := WordEventSystem.Block.single graphSystem (atomic_toggle_inc k rows base 0 0 0 0 0 0 reserve)
    simpa using h1.trans graphSystem h2
  | true =>
    have h1 := WordEventSystem.Block.single graphSystem (atomic_toggle_dec k rows base 0 0 0 0 0 0 reserve)
    have h2 := WordEventSystem.Block.single graphSystem (atomic_toggle_jump k rows base 0 0 0 0 0 0 (reserve ++ [0]))
    simpa using h1.trans graphSystem h2

/-- The positive atom phase stores the Boolean complement in top. -/
theorem atomic_toggle_then_store (k : Nat) (rows : AtomicToggleRows k) (store : AtomicStoreRows (k+3))
    (base : RegisterMachine.Bank 9) (bit : Bool) (reserve : List Nat) :
    graphSystem.Block (cfgAtom k base 0 0 0 (if bit then 1 else 0) 0 0 reserve)
      (if bit then 4 else 7)
      (cfgAtom 724 base (if !bit then 1 else 0) 0 0 0 0 0 (reserve ++ [0])) [] := by
  cases bit with
  | false =>
    have h1 := atomic_toggle_bool k rows base false reserve
    have h2 := atomic_store_bool (k+3) store base true reserve
    simp only [Bool.false_eq_true, Bool.not_false, ↓reduceIte, List.append_nil] at h1 h2
    simpa using h1.trans graphSystem h2
  | true =>
    have h1 := atomic_toggle_bool k rows base true reserve
    have h2 := atomic_store_bool (k+3) store base false (reserve ++ [0])
    simp only [Bool.not_true, ↓reduceIte] at h1 h2
    simpa using h1.trans graphSystem h2

/-- Negative-sign atom: the payoff is the atom value itself. -/
theorem atomic_negative_payoff (payload encoded k : Nat)
    (first : AtomFirstLookupRows k) (second : AtomSecondLookupRows (k+29))
    (bits : AtomicBitRows (k+66)) (store : AtomicStoreRows (k+92))
    (base : RegisterMachine.Bank 9) (reserve : List Nat) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block
        (cfgAtom k base (Cantor.unpair payload).2 encoded (Cantor.unpair payload).1 0 0 0 reserve) duration
        (cfgAtom 724 base (if M236Game.encodedAtom payload encoded then 1 else 0) 0 0 0 0 0
          (reserve ++ List.replicate padding 0)) [] := by
  obtain ⟨firstDuration, firstPadding, hf, h1⟩ := atomic_operands_to_bit payload encoded k first second bits base reserve
  have h2 := atomic_store_bool (k+92) store base (M236Game.encodedAtom payload encoded)
    (reserve ++ List.replicate firstPadding 0)
  have h := h1.trans graphSystem h2
  refine ⟨firstDuration+(if M236Game.encodedAtom payload encoded then 5 else 2),
    firstPadding+(if M236Game.encodedAtom payload encoded then 1 else 0), ?_, ?_⟩
  · cases M236Game.encodedAtom payload encoded <;> simp_all
  · have hr : (reserve ++ List.replicate firstPadding 0) ++
        (if M236Game.encodedAtom payload encoded then [0] else []) =
        reserve ++ List.replicate (firstPadding+(if M236Game.encodedAtom payload encoded then 1 else 0)) 0 := by
      cases M236Game.encodedAtom payload encoded <;> simp [List.replicate_add, List.append_assoc]
    simp only [List.nil_append] at h
    rw [hr] at h
    exact h

/-- Positive-sign atom: the payoff is the complement of the atom value. -/
theorem atomic_positive_payoff (payload encoded k : Nat)
    (first : AtomFirstLookupRows k) (second : AtomSecondLookupRows (k+29))
    (bits : AtomicBitRows (k+66)) (toggle : AtomicToggleRows (k+92))
    (store : AtomicStoreRows (k+95)) (base : RegisterMachine.Bank 9) (reserve : List Nat) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block
        (cfgAtom k base (Cantor.unpair payload).2 encoded (Cantor.unpair payload).1 0 0 0 reserve) duration
        (cfgAtom 724 base (if !M236Game.encodedAtom payload encoded then 1 else 0) 0 0 0 0 0
          (reserve ++ List.replicate padding 0)) [] := by
  obtain ⟨firstDuration, firstPadding, hf, h1⟩ := atomic_operands_to_bit payload encoded k first second bits base reserve
  have hstore : AtomicStoreRows ((k+92)+3) := by simpa [Nat.add_assoc] using store
  have h2 := atomic_toggle_then_store (k+92) toggle hstore base (M236Game.encodedAtom payload encoded)
    (reserve ++ List.replicate firstPadding 0)
  have h := h1.trans graphSystem h2
  refine ⟨firstDuration+(if M236Game.encodedAtom payload encoded then 4 else 7), firstPadding+1, ?_, ?_⟩
  · cases M236Game.encodedAtom payload encoded <;> simp_all
  · have hr : (reserve ++ List.replicate firstPadding 0) ++ [0] =
        reserve ++ List.replicate (firstPadding+1) 0 := by
      simp [List.replicate_add, List.append_assoc]
    simp only [List.nil_append] at h
    rw [hr] at h
    exact h

/-- The initial negative-sign atomic occurrence. -/
theorem atomic_negative_payoff_270 (payload encoded : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block
        (cfgAtom 270 base (Cantor.unpair payload).2 encoded (Cantor.unpair payload).1 0 0 0 reserve) duration
        (cfgAtom 724 base (if M236Game.encodedAtom payload encoded then 1 else 0) 0 0 0 0 0
          (reserve ++ List.replicate padding 0)) [] := by
  exact atomic_negative_payoff payload encoded 270 atom_first_lookup_rows_270 atom_second_lookup_rows_299
    atomic_bit_rows_336 atomic_store_rows_362 base reserve

/-- The positive-sign atomic occurrence. -/
theorem atomic_positive_payoff_447 (payload encoded : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block
        (cfgAtom 447 base (Cantor.unpair payload).2 encoded (Cantor.unpair payload).1 0 0 0 reserve) duration
        (cfgAtom 724 base (if !M236Game.encodedAtom payload encoded then 1 else 0) 0 0 0 0 0
          (reserve ++ List.replicate padding 0)) [] := by
  exact atomic_positive_payoff payload encoded 447 atom_first_lookup_rows_447 atom_second_lookup_rows_476
    atomic_bit_rows_513 atomic_toggle_rows_539 atomic_store_rows_542 base reserve

/-- The recurring negative-sign atomic occurrence. -/
theorem atomic_negative_payoff_627 (payload encoded : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block
        (cfgAtom 627 base (Cantor.unpair payload).2 encoded (Cantor.unpair payload).1 0 0 0 reserve) duration
        (cfgAtom 724 base (if M236Game.encodedAtom payload encoded then 1 else 0) 0 0 0 0 0
          (reserve ++ List.replicate padding 0)) [] := by
  exact atomic_negative_payoff payload encoded 627 atom_first_lookup_rows_627 atom_second_lookup_rows_656
    atomic_bit_rows_693 atomic_store_rows_719 base reserve

/-- Lift a prepared graph atom block to the literal blank-start execution;
the hypothesis explicitly states that this prepared entry is reached. -/
theorem selected_atomic_payoff_of_block (i payload encoded k : Nat) (output : Bool)
    (base : RegisterMachine.Bank 9) (reserve : List Nat)
    (h : graphSystem.run i =
      cfgAtom k base (Cantor.unpair payload).2 encoded (Cantor.unpair payload).1 0 0 0 reserve)
    (block : ∃ duration padding, 0 < duration ∧
      graphSystem.Block
        (cfgAtom k base (Cantor.unpair payload).2 encoded (Cantor.unpair payload).1 0 0 0 reserve) duration
        (cfgAtom 724 base (if output then 1 else 0) 0 0 0 0 0
          (reserve ++ List.replicate padding 0)) []) :
    ∃ duration padding finish, 0 < duration ∧ Good finish ∧
      finish.graphState = cfgAtom 724 base (if output then 1 else 0) 0 0 0 0 0
        (reserve ++ List.replicate padding 0) ∧
      graphSystem.run (i+duration) = cfgAtom 724 base (if output then 1 else 0) 0 0 0 0 0
        (reserve ++ List.replicate padding 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i+duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i+duration) := by
  obtain ⟨duration, padding, ht, hb⟩ := block
  have hr : graphSystem.run (i+duration) = cfgAtom 724 base (if output then 1 else 0) 0 0 0 0 0
      (reserve ++ List.replicate padding 0) := by
    rw [WordEventSystem.run_add, h, hb.endpoint]
  have hp : graphSystem.prefixWord (i+duration) = graphSystem.prefixWord i := by
    rw [WordEventSystem.prefix_add, h, hb.output, List.append_nil]
  obtain ⟨finish, hg, hs, hconfig⟩ := graphRefinement.related (i+duration)
  refine ⟨duration, padding, finish, ht, hg, hs.trans hr, hr, hconfig, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

/-- Concrete negative-phase graph block and its reached-entry physical lift. -/
theorem selected_atomic_negative_270 (i payload encoded : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (h : graphSystem.run i =
      cfgAtom 270 base (Cantor.unpair payload).2 encoded (Cantor.unpair payload).1 0 0 0 reserve) :
    ∃ duration padding finish, 0 < duration ∧ Good finish ∧
      finish.graphState = cfgAtom 724 base (if M236Game.encodedAtom payload encoded then 1 else 0) 0 0 0 0 0
        (reserve ++ List.replicate padding 0) ∧
      graphSystem.run (i+duration) = cfgAtom 724 base (if M236Game.encodedAtom payload encoded then 1 else 0) 0 0 0 0 0
        (reserve ++ List.replicate padding 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run (graphRefinement.boundary (i+duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i+duration) := by
  exact selected_atomic_payoff_of_block i payload encoded 270 (M236Game.encodedAtom payload encoded)
    base reserve h (atomic_negative_payoff_270 payload encoded base reserve)

/-- Concrete positive-phase graph block and its reached-entry physical lift. -/
theorem selected_atomic_positive_447 (i payload encoded : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (h : graphSystem.run i =
      cfgAtom 447 base (Cantor.unpair payload).2 encoded (Cantor.unpair payload).1 0 0 0 reserve) :
    ∃ duration padding finish, 0 < duration ∧ Good finish ∧
      finish.graphState = cfgAtom 724 base (if !M236Game.encodedAtom payload encoded then 1 else 0) 0 0 0 0 0
        (reserve ++ List.replicate padding 0) ∧
      graphSystem.run (i+duration) = cfgAtom 724 base (if !M236Game.encodedAtom payload encoded then 1 else 0) 0 0 0 0 0
        (reserve ++ List.replicate padding 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run (graphRefinement.boundary (i+duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i+duration) := by
  exact selected_atomic_payoff_of_block i payload encoded 447 (!M236Game.encodedAtom payload encoded)
    base reserve h (atomic_positive_payoff_447 payload encoded base reserve)

/-- Recurring negative-phase graph block and its reached-entry physical lift. -/
theorem selected_atomic_negative_627 (i payload encoded : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (h : graphSystem.run i =
      cfgAtom 627 base (Cantor.unpair payload).2 encoded (Cantor.unpair payload).1 0 0 0 reserve) :
    ∃ duration padding finish, 0 < duration ∧ Good finish ∧
      finish.graphState = cfgAtom 724 base (if M236Game.encodedAtom payload encoded then 1 else 0) 0 0 0 0 0
        (reserve ++ List.replicate padding 0) ∧
      graphSystem.run (i+duration) = cfgAtom 724 base (if M236Game.encodedAtom payload encoded then 1 else 0) 0 0 0 0 0
        (reserve ++ List.replicate padding 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run (graphRefinement.boundary (i+duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i+duration) := by
  exact selected_atomic_payoff_of_block i payload encoded 627 (M236Game.encodedAtom payload encoded)
    base reserve h (atomic_negative_payoff_627 payload encoded base reserve)

end PASoundness.M236.OccurrenceGraph
