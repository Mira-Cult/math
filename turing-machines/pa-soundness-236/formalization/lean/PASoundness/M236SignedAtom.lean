import PASoundness.M236AtomicBit
import PASoundness.M236SignedNonatomic
import PASoundness.M236ResidualEntry
import PASoundness.M236FinalCleanup

/-! Prepared zero-tag atomic setup and signed payoff at all graph occurrences. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

structure AtomSetupRows (k : Nat) : Prop where
  decA : sourceRows[k]? = some ("3.k.a.decnz", k+1, some (k+2))
  jumpA : sourceRows[k+1]? = some ("jump", k, none)
  decS : sourceRows[k+2]? = some ("3.scratch.copy.decnz", k+3, some (k+5))
  incB : sourceRows[k+3]? = some ("3.k.b.inc", k+4, none)
  jumpS : sourceRows[k+4]? = some ("jump", k+2, none)
  scan : FormulaScanRows (k+5)
  decC : sourceRows[k+13]? = some ("3.k.c.decnz", k+14, some (k+16))
  incA : sourceRows[k+14]? = some ("3.k.a.inc", k+15, none)
  jumpC : sourceRows[k+15]? = some ("jump", k+13, none)
  decS2 : sourceRows[k+16]? = some ("3.scratch.copy.decnz", k+17, some (k+19))
  incTop : sourceRows[k+17]? = some ("3.k.top.inc", k+18, none)
  jumpS2 : sourceRows[k+18]? = some ("jump", k+16, none)

theorem atom_setup_rows_251 : AtomSetupRows 251 := by constructor <;> first | constructor <;> decide
theorem atom_setup_rows_428 : AtomSetupRows 428 := by constructor <;> first | constructor <;> decide
theorem atom_setup_rows_608 : AtomSetupRows 608 := by constructor <;> first | constructor <;> decide

theorem atom_setup_s_b_dec (k : Nat) (rows : AtomSetupRows k) (base : RegisterMachine.Bank 9)
    (a b c s top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgSelect (k+2) base a b c (s+1) top reserve) = (cfgSelect (k+3) base a b c s top (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgSelect, rows.decS, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankSelect, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem atom_setup_s_b_zero (k : Nat) (rows : AtomSetupRows k) (base : RegisterMachine.Bank 9)
    (a b c _s top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgSelect (k+2) base a b c 0 top reserve) = (cfgSelect (k+5) base a b c 0 top reserve, []) := by
  simp [graphSystem, graphNext, cfgSelect, rows.decS, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankSelect, bankHalf, RegisterMachine.execute]

theorem atom_setup_s_b_inc (k : Nat) (rows : AtomSetupRows k) (base : RegisterMachine.Bank 9)
    (a b c s top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgSelect (k+3) base a b c s top reserve) = (cfgSelect (k+4) base a (b+1) c s top reserve, []) := by
  simp [graphSystem, graphNext, cfgSelect, rows.incB, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankSelect, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem atom_setup_s_b_jump (k : Nat) (rows : AtomSetupRows k) (base : RegisterMachine.Bank 9)
    (a b c s top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgSelect (k+4) base a b c s top reserve) = (cfgSelect (k+2) base a b c s top reserve, []) := by
  simp [graphSystem, graphNext, cfgSelect, rows.jumpS, nextIndex, nextBank, nextReserve, incRegister, decRegister, outputForOp]

theorem atom_setup_s_b_cycle (k : Nat) (rows : AtomSetupRows k) (base : RegisterMachine.Bank 9)
    (a b c s top : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgSelect (k+2) base a b c (s+1) top reserve) 3 (cfgSelect (k+2) base a (b+1) c s top (reserve ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (atom_setup_s_b_dec k rows base a b c s top reserve)
  have h2 := WordEventSystem.Block.single graphSystem (atom_setup_s_b_inc k rows base a b c s top (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (atom_setup_s_b_jump k rows base a (b+1) c s top (reserve ++ [0]))
  simpa using (h1.trans graphSystem h2).trans graphSystem h3

theorem atom_setup_s_b_many (n k : Nat) (rows : AtomSetupRows k) (base : RegisterMachine.Bank 9)
    (a b c top : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgSelect (k+2) base a b c n top reserve) (3*n)
      (cfgSelect (k+2) base a (b+n) c 0 top (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing b reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgSelect (k+2) base a b c 0 top reserve)
  | succ n ih =>
    have h := (atom_setup_s_b_cycle k rows base a b c n top reserve).trans graphSystem (ih (b+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem atom_setup_s_b_move (n k : Nat) (rows : AtomSetupRows k) (base : RegisterMachine.Bank 9)
    (a b c top : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgSelect (k+2) base a b c n top reserve) (3*n+1)
      (cfgSelect (k+5) base a (b+n) c 0 top (reserve ++ List.replicate n 0)) [] := by
  have h := (atom_setup_s_b_many n k rows base a b c top reserve).trans graphSystem
    (WordEventSystem.Block.single graphSystem (atom_setup_s_b_zero k rows base a (b+n) c 0 top (reserve ++ List.replicate n 0)))
  simpa using h

theorem atom_setup_c_a_dec (k : Nat) (rows : AtomSetupRows k) (base : RegisterMachine.Bank 9)
    (a b c s top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgSelect (k+13) base a b (c+1) s top reserve) = (cfgSelect (k+14) base a b c s top (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgSelect, rows.decC, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankSelect, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem atom_setup_c_a_zero (k : Nat) (rows : AtomSetupRows k) (base : RegisterMachine.Bank 9)
    (a b _c s top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgSelect (k+13) base a b 0 s top reserve) = (cfgSelect (k+16) base a b 0 s top reserve, []) := by
  simp [graphSystem, graphNext, cfgSelect, rows.decC, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankSelect, bankHalf, RegisterMachine.execute]

theorem atom_setup_c_a_inc (k : Nat) (rows : AtomSetupRows k) (base : RegisterMachine.Bank 9)
    (a b c s top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgSelect (k+14) base a b c s top reserve) = (cfgSelect (k+15) base (a+1) b c s top reserve, []) := by
  simp [graphSystem, graphNext, cfgSelect, rows.incA, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankSelect, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem atom_setup_c_a_jump (k : Nat) (rows : AtomSetupRows k) (base : RegisterMachine.Bank 9)
    (a b c s top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgSelect (k+15) base a b c s top reserve) = (cfgSelect (k+13) base a b c s top reserve, []) := by
  simp [graphSystem, graphNext, cfgSelect, rows.jumpC, nextIndex, nextBank, nextReserve, incRegister, decRegister, outputForOp]

theorem atom_setup_c_a_cycle (k : Nat) (rows : AtomSetupRows k) (base : RegisterMachine.Bank 9)
    (a b c s top : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgSelect (k+13) base a b (c+1) s top reserve) 3 (cfgSelect (k+13) base (a+1) b c s top (reserve ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (atom_setup_c_a_dec k rows base a b c s top reserve)
  have h2 := WordEventSystem.Block.single graphSystem (atom_setup_c_a_inc k rows base a b c s top (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (atom_setup_c_a_jump k rows base (a+1) b c s top (reserve ++ [0]))
  simpa using (h1.trans graphSystem h2).trans graphSystem h3

theorem atom_setup_c_a_many (n k : Nat) (rows : AtomSetupRows k) (base : RegisterMachine.Bank 9)
    (a b s top : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgSelect (k+13) base a b n s top reserve) (3*n)
      (cfgSelect (k+13) base (a+n) b 0 s top (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing a reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgSelect (k+13) base a b 0 s top reserve)
  | succ n ih =>
    have h := (atom_setup_c_a_cycle k rows base a b n s top reserve).trans graphSystem (ih (a+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem atom_setup_c_a_move (n k : Nat) (rows : AtomSetupRows k) (base : RegisterMachine.Bank 9)
    (a b s top : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgSelect (k+13) base a b n s top reserve) (3*n+1)
      (cfgSelect (k+16) base (a+n) b 0 s top (reserve ++ List.replicate n 0)) [] := by
  have h := (atom_setup_c_a_many n k rows base a b s top reserve).trans graphSystem
    (WordEventSystem.Block.single graphSystem (atom_setup_c_a_zero k rows base (a+n) b 0 s top (reserve ++ List.replicate n 0)))
  simpa using h

theorem atom_setup_s_top_dec (k : Nat) (rows : AtomSetupRows k) (base : RegisterMachine.Bank 9)
    (a b c s top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgSelect (k+16) base a b c (s+1) top reserve) = (cfgSelect (k+17) base a b c s top (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgSelect, rows.decS2, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankSelect, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem atom_setup_s_top_zero (k : Nat) (rows : AtomSetupRows k) (base : RegisterMachine.Bank 9)
    (a b c _s top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgSelect (k+16) base a b c 0 top reserve) = (cfgSelect (k+19) base a b c 0 top reserve, []) := by
  simp [graphSystem, graphNext, cfgSelect, rows.decS2, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankSelect, bankHalf, RegisterMachine.execute]

theorem atom_setup_s_top_inc (k : Nat) (rows : AtomSetupRows k) (base : RegisterMachine.Bank 9)
    (a b c s top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgSelect (k+17) base a b c s top reserve) = (cfgSelect (k+18) base a b c s (top+1) reserve, []) := by
  simp [graphSystem, graphNext, cfgSelect, rows.incTop, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankSelect, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem atom_setup_s_top_jump (k : Nat) (rows : AtomSetupRows k) (base : RegisterMachine.Bank 9)
    (a b c s top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgSelect (k+18) base a b c s top reserve) = (cfgSelect (k+16) base a b c s top reserve, []) := by
  simp [graphSystem, graphNext, cfgSelect, rows.jumpS2, nextIndex, nextBank, nextReserve, incRegister, decRegister, outputForOp]

theorem atom_setup_s_top_cycle (k : Nat) (rows : AtomSetupRows k) (base : RegisterMachine.Bank 9)
    (a b c s top : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgSelect (k+16) base a b c (s+1) top reserve) 3 (cfgSelect (k+16) base a b c s (top+1) (reserve ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (atom_setup_s_top_dec k rows base a b c s top reserve)
  have h2 := WordEventSystem.Block.single graphSystem (atom_setup_s_top_inc k rows base a b c s top (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (atom_setup_s_top_jump k rows base a b c s (top+1) (reserve ++ [0]))
  simpa using (h1.trans graphSystem h2).trans graphSystem h3

theorem atom_setup_s_top_many (n k : Nat) (rows : AtomSetupRows k) (base : RegisterMachine.Bank 9)
    (a b c top : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgSelect (k+16) base a b c n top reserve) (3*n)
      (cfgSelect (k+16) base a b c 0 (top+n) (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing top reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgSelect (k+16) base a b c 0 top reserve)
  | succ n ih =>
    have h := (atom_setup_s_top_cycle k rows base a b c n top reserve).trans graphSystem (ih (top+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem atom_setup_s_top_move (n k : Nat) (rows : AtomSetupRows k) (base : RegisterMachine.Bank 9)
    (a b c top : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgSelect (k+16) base a b c n top reserve) (3*n+1)
      (cfgSelect (k+19) base a b c 0 (top+n) (reserve ++ List.replicate n 0)) [] := by
  have h := (atom_setup_s_top_many n k rows base a b c top reserve).trans graphSystem
    (WordEventSystem.Block.single graphSystem (atom_setup_s_top_zero k rows base a b c 0 (top+n) (reserve ++ List.replicate n 0)))
  simpa using h

theorem atom_setup_a_dec (k : Nat) (rows : AtomSetupRows k) (base : RegisterMachine.Bank 9)
    (a b c s top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgSelect k base (a+1) b c s top reserve) =
      (cfgSelect (k+1) base a b c s top (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgSelect, rows.decA, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankSelect, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem atom_setup_a_zero (k : Nat) (rows : AtomSetupRows k) (base : RegisterMachine.Bank 9)
    (b c s top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgSelect k base 0 b c s top reserve) = (cfgSelect (k+2) base 0 b c s top reserve, []) := by
  simp [graphSystem, graphNext, cfgSelect, rows.decA, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankSelect, bankHalf, RegisterMachine.execute]

theorem atom_setup_a_jump (k : Nat) (rows : AtomSetupRows k) (base : RegisterMachine.Bank 9)
    (a b c s top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgSelect (k+1) base a b c s top reserve) = (cfgSelect k base a b c s top reserve, []) := by
  simp [graphSystem, graphNext, cfgSelect, rows.jumpA, nextIndex, nextBank, nextReserve, incRegister, decRegister, outputForOp]

theorem atom_setup_clear_a (n k : Nat) (rows : AtomSetupRows k) (base : RegisterMachine.Bank 9)
    (b c s top : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgSelect k base n b c s top reserve) (2*n+1)
      (cfgSelect (k+2) base 0 b c s top (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing reserve with
  | zero => simpa using WordEventSystem.Block.single graphSystem (atom_setup_a_zero k rows base b c s top reserve)
  | succ n ih =>
    have h1 := WordEventSystem.Block.single graphSystem (atom_setup_a_dec k rows base n b c s top reserve)
    have h2 := WordEventSystem.Block.single graphSystem (atom_setup_a_jump k rows base n b c s top (reserve ++ [0]))
    have h := (h1.trans graphSystem h2).trans graphSystem (ih (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

/-- Starting at the tag-zero branch, consume the paid move, unpair the
payload, and prepare both atomic-lookup indices. -/
theorem atom_setup (k : Nat) (rows : AtomSetupRows k) (base : RegisterMachine.Bank 9)
    (move payload : Nat) (reserve : List Nat) :
    ∃ duration padding, payload+1 ≤ duration ∧
      graphSystem.Block (cfgSelect k base move 0 0 payload 0 reserve) duration
        (cfgSelect (k+19) base (Cantor.unpair payload).1 0 0 0 (Cantor.unpair payload).2
          (reserve ++ List.replicate padding 0)) [] := by
  have h1 := atom_setup_clear_a move k rows base 0 0 payload 0 reserve
  have h2 := atom_setup_s_b_move payload k rows base 0 0 0 0 (reserve ++ List.replicate move 0)
  simp only [Nat.zero_add] at h2
  obtain ⟨duration, padding, ht, h3⟩ := formula_diagonal_unpair 0 payload (k+5) rows.scan
    (RegisterMachine.write base 4 0) ((reserve ++ List.replicate move 0) ++ List.replicate payload 0)
  change graphSystem.Block (cfgSelect (k+5) base 0 payload 0 0 0
      ((reserve ++ List.replicate move 0) ++ List.replicate payload 0)) duration
    (cfgSelect (k+13) base 0 0 (Cantor.unpair payload).1 (Cantor.unpair payload).2 0
      (((reserve ++ List.replicate move 0) ++ List.replicate payload 0) ++ List.replicate padding 0)) [] at h3
  have h4 := atom_setup_c_a_move (Cantor.unpair payload).1 k rows base 0 0
    (Cantor.unpair payload).2 0
    (((reserve ++ List.replicate move 0) ++ List.replicate payload 0) ++ List.replicate padding 0)
  simp only [Nat.zero_add] at h4
  have h5 := atom_setup_s_top_move (Cantor.unpair payload).2 k rows base
    (Cantor.unpair payload).1 0 0 0
    ((((reserve ++ List.replicate move 0) ++ List.replicate payload 0) ++ List.replicate padding 0) ++
      List.replicate (Cantor.unpair payload).1 0)
  simp only [Nat.zero_add] at h5
  have h := (((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4).trans graphSystem h5
  refine ⟨2*move+1+(3*payload+1)+duration+(3*(Cantor.unpair payload).1+1)+
      (3*(Cantor.unpair payload).2+1),
    move+payload+padding+(Cantor.unpair payload).1+(Cantor.unpair payload).2, by omega, ?_⟩
  have hr : ((((reserve ++ List.replicate move 0) ++ List.replicate payload 0) ++ List.replicate padding 0) ++
      List.replicate (Cantor.unpair payload).1 0) ++ List.replicate (Cantor.unpair payload).2 0 =
        reserve ++ List.replicate (move+payload+padding+(Cantor.unpair payload).1+(Cantor.unpair payload).2) 0 := by
    simp only [List.replicate_add, List.append_assoc]
  simp only [List.nil_append] at h
  rw [hr] at h
  exact h

theorem atom_select_view (i : Nat) (base : RegisterMachine.Bank 9) (a b c scratch top : Nat)
    (reserve : List Nat) :
    cfgSelect i base a b c scratch top reserve = cfgAtom i base top (base 5) a b c scratch reserve := by
  unfold cfgSelect cfgAtom cfgEnv cfgHalf bankSelect
  congr 1
  funext j
  fin_cases j <;> simp [bankHalf, RegisterMachine.write]

/-- A tag-zero formula at a prepared negative-phase scan evaluates the paid
atom slot and stores its encoded atomic value as the payoff. -/
theorem signed_atom_negative (formula move k : Nat) (scan : FormulaScanRows k) (branch : FormulaBranchRow k)
    (setup : AtomSetupRows (k+35)) (first : AtomFirstLookupRows (k+54))
    (second : AtomSecondLookupRows ((k+54)+29)) (bits : AtomicBitRows ((k+54)+66))
    (store : AtomicStoreRows ((k+54)+92)) (base : RegisterMachine.Bank 9) (reserve : List Nat)
    (htag : (Cantor.unpair formula).1 = 0) (htop : base 4 = 0) :
    ∃ duration padding, formula+2 ≤ duration ∧
      graphSystem.Block (cfgHalf k base move formula 0 0 reserve) duration
        (cfgAtom 724 base (if M236Game.encodedAtom (Cantor.unpair formula).2 (base 5) then 1 else 0)
          0 0 0 0 0 (reserve ++ List.replicate padding 0)) [] := by
  obtain ⟨d1, p1, hd1, h1⟩ := formula_unpair_zero_branch move formula k scan branch base reserve htag
  rw [half_to_child_view (k+35) base move 0 0 (Cantor.unpair formula).2 _, htop] at h1
  obtain ⟨d2, p2, hd2, h2⟩ := atom_setup (k+35) setup base move (Cantor.unpair formula).2
    (reserve ++ List.replicate p1 0)
  change graphSystem.Block (cfgSelect (k+35) base move 0 0 (Cantor.unpair formula).2 0
      (reserve ++ List.replicate p1 0)) d2
    (cfgSelect (k+54) base (Cantor.unpair (Cantor.unpair formula).2).1 0 0 0
      (Cantor.unpair (Cantor.unpair formula).2).2
      ((reserve ++ List.replicate p1 0) ++ List.replicate p2 0)) [] at h2
  rw [atom_select_view (k+54) base (Cantor.unpair (Cantor.unpair formula).2).1 0 0 0
    (Cantor.unpair (Cantor.unpair formula).2).2 _] at h2
  obtain ⟨d3, p3, hd3, h3⟩ := atomic_negative_payoff (Cantor.unpair formula).2 (base 5) (k+54)
    first second bits store base ((reserve ++ List.replicate p1 0) ++ List.replicate p2 0)
  have h := (h1.trans graphSystem h2).trans graphSystem h3
  refine ⟨d1+d2+d3, p1+p2+p3, by omega, ?_⟩
  have hr : ((reserve ++ List.replicate p1 0) ++ List.replicate p2 0) ++ List.replicate p3 0 =
      reserve ++ List.replicate (p1+p2+p3) 0 := by simp only [List.replicate_add, List.append_assoc]
  simp only [List.nil_append] at h
  rw [hr] at h
  exact h

/-- Positive-phase tag-zero atoms store the complemented encoded atomic value. -/
theorem signed_atom_positive (formula move k : Nat) (scan : FormulaScanRows k) (branch : FormulaBranchRow k)
    (setup : AtomSetupRows (k+35)) (first : AtomFirstLookupRows (k+54))
    (second : AtomSecondLookupRows ((k+54)+29)) (bits : AtomicBitRows ((k+54)+66))
    (toggle : AtomicToggleRows ((k+54)+92)) (store : AtomicStoreRows ((k+54)+95))
    (base : RegisterMachine.Bank 9) (reserve : List Nat)
    (htag : (Cantor.unpair formula).1 = 0) (htop : base 4 = 0) :
    ∃ duration padding, formula+2 ≤ duration ∧
      graphSystem.Block (cfgHalf k base move formula 0 0 reserve) duration
        (cfgAtom 724 base (if !M236Game.encodedAtom (Cantor.unpair formula).2 (base 5) then 1 else 0)
          0 0 0 0 0 (reserve ++ List.replicate padding 0)) [] := by
  obtain ⟨d1, p1, hd1, h1⟩ := formula_unpair_zero_branch move formula k scan branch base reserve htag
  rw [half_to_child_view (k+35) base move 0 0 (Cantor.unpair formula).2 _, htop] at h1
  obtain ⟨d2, p2, hd2, h2⟩ := atom_setup (k+35) setup base move (Cantor.unpair formula).2
    (reserve ++ List.replicate p1 0)
  change graphSystem.Block (cfgSelect (k+35) base move 0 0 (Cantor.unpair formula).2 0
      (reserve ++ List.replicate p1 0)) d2
    (cfgSelect (k+54) base (Cantor.unpair (Cantor.unpair formula).2).1 0 0 0
      (Cantor.unpair (Cantor.unpair formula).2).2
      ((reserve ++ List.replicate p1 0) ++ List.replicate p2 0)) [] at h2
  rw [atom_select_view (k+54) base (Cantor.unpair (Cantor.unpair formula).2).1 0 0 0
    (Cantor.unpair (Cantor.unpair formula).2).2 _] at h2
  obtain ⟨d3, p3, hd3, h3⟩ := atomic_positive_payoff (Cantor.unpair formula).2 (base 5) (k+54)
    first second bits toggle store base ((reserve ++ List.replicate p1 0) ++ List.replicate p2 0)
  have h := (h1.trans graphSystem h2).trans graphSystem h3
  refine ⟨d1+d2+d3, p1+p2+p3, by omega, ?_⟩
  have hr : ((reserve ++ List.replicate p1 0) ++ List.replicate p2 0) ++ List.replicate p3 0 =
      reserve ++ List.replicate (p1+p2+p3) 0 := by simp only [List.replicate_add, List.append_assoc]
  simp only [List.nil_append] at h
  rw [hr] at h
  exact h

/-- The explicitly paid atomic move is ignored, but it must be present; the
returned Boolean is the complement of the corresponding signed path value. -/
theorem paid_atom_payoff (formula encoded move : Nat) (moves : List Nat) (negative : Bool)
    (htag : (Cantor.unpair formula).1 = 0) :
    !M236Game.encodedPath formula encoded negative (move :: moves) =
      (M236Game.encodedAtom (Cantor.unpair formula).2 encoded == negative) := by
  rw [M236Game.encodedPath]
  simp only [M236Game.tag, htag, ↓reduceDIte, M236Game.payload]
  cases negative <;> cases M236Game.encodedAtom (Cantor.unpair formula).2 encoded <;> rfl

theorem signed_atom_negative_216 (formula move : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (htag : (Cantor.unpair formula).1 = 0) (htop : base 4 = 0) :
    ∃ duration padding, formula+2 ≤ duration ∧
      graphSystem.Block (cfgHalf 216 base move formula 0 0 reserve) duration
        (cfgAtom 724 base (if M236Game.encodedAtom (Cantor.unpair formula).2 (base 5) then 1 else 0)
          0 0 0 0 0 (reserve ++ List.replicate padding 0)) [] := by
  exact signed_atom_negative formula move 216 formula_scan_rows_216 formula_branch_row_216
    atom_setup_rows_251 atom_first_lookup_rows_270 atom_second_lookup_rows_299 atomic_bit_rows_336
    atomic_store_rows_362 base reserve htag htop

theorem signed_atom_positive_393 (formula move : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (htag : (Cantor.unpair formula).1 = 0) (htop : base 4 = 0) :
    ∃ duration padding, formula+2 ≤ duration ∧
      graphSystem.Block (cfgHalf 393 base move formula 0 0 reserve) duration
        (cfgAtom 724 base (if !M236Game.encodedAtom (Cantor.unpair formula).2 (base 5) then 1 else 0)
          0 0 0 0 0 (reserve ++ List.replicate padding 0)) [] := by
  exact signed_atom_positive formula move 393 formula_scan_rows_393 formula_branch_row_393
    atom_setup_rows_428 atom_first_lookup_rows_447 atom_second_lookup_rows_476 atomic_bit_rows_513
    atomic_toggle_rows_539 atomic_store_rows_542 base reserve htag htop

theorem signed_atom_negative_573 (formula move : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (htag : (Cantor.unpair formula).1 = 0) (htop : base 4 = 0) :
    ∃ duration padding, formula+2 ≤ duration ∧
      graphSystem.Block (cfgHalf 573 base move formula 0 0 reserve) duration
        (cfgAtom 724 base (if M236Game.encodedAtom (Cantor.unpair formula).2 (base 5) then 1 else 0)
          0 0 0 0 0 (reserve ++ List.replicate padding 0)) [] := by
  exact signed_atom_negative formula move 573 formula_scan_rows_573 formula_branch_row_573
    atom_setup_rows_608 atom_first_lookup_rows_627 atom_second_lookup_rows_656 atomic_bit_rows_693
    atomic_store_rows_719 base reserve htag htop

/-- A silent prepared signed-atom graph block lifts to the actual selected
physical run if the specified formula-scan entry is reached. -/
theorem selected_signed_atom_of_block (i formula move k : Nat) (output : Bool)
    (base : RegisterMachine.Bank 9) (reserve : List Nat)
    (h : graphSystem.run i = cfgHalf k base move formula 0 0 reserve)
    (block : ∃ duration padding, formula+2 ≤ duration ∧
      graphSystem.Block (cfgHalf k base move formula 0 0 reserve) duration
        (cfgAtom 724 base (if output then 1 else 0) 0 0 0 0 0 (reserve ++ List.replicate padding 0)) []) :
    ∃ duration padding finish, formula+2 ≤ duration ∧ Good finish ∧
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

/-- Concrete physical negative-atom step conditional on reaching entry 216. -/
theorem selected_signed_atom_negative_216 (i formula move : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (htag : (Cantor.unpair formula).1 = 0) (htop : base 4 = 0)
    (h : graphSystem.run i = cfgHalf 216 base move formula 0 0 reserve) :
    ∃ duration padding finish, formula+2 ≤ duration ∧ Good finish ∧
      finish.graphState = cfgAtom 724 base (if M236Game.encodedAtom (Cantor.unpair formula).2 (base 5) then 1 else 0)
        0 0 0 0 0 (reserve ++ List.replicate padding 0) ∧
      graphSystem.run (i+duration) = cfgAtom 724 base (if M236Game.encodedAtom (Cantor.unpair formula).2 (base 5) then 1 else 0)
        0 0 0 0 0 (reserve ++ List.replicate padding 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run (graphRefinement.boundary (i+duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i+duration) := by
  exact selected_signed_atom_of_block i formula move 216 (M236Game.encodedAtom (Cantor.unpair formula).2 (base 5))
    base reserve h (signed_atom_negative_216 formula move base reserve htag htop)

/-- Concrete physical positive-atom step conditional on reaching entry 393. -/
theorem selected_signed_atom_positive_393 (i formula move : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (htag : (Cantor.unpair formula).1 = 0) (htop : base 4 = 0)
    (h : graphSystem.run i = cfgHalf 393 base move formula 0 0 reserve) :
    ∃ duration padding finish, formula+2 ≤ duration ∧ Good finish ∧
      finish.graphState = cfgAtom 724 base (if !M236Game.encodedAtom (Cantor.unpair formula).2 (base 5) then 1 else 0)
        0 0 0 0 0 (reserve ++ List.replicate padding 0) ∧
      graphSystem.run (i+duration) = cfgAtom 724 base (if !M236Game.encodedAtom (Cantor.unpair formula).2 (base 5) then 1 else 0)
        0 0 0 0 0 (reserve ++ List.replicate padding 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run (graphRefinement.boundary (i+duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i+duration) := by
  exact selected_signed_atom_of_block i formula move 393 (!M236Game.encodedAtom (Cantor.unpair formula).2 (base 5))
    base reserve h (signed_atom_positive_393 formula move base reserve htag htop)

/-- Recurring physical negative-atom step conditional on reaching entry 573. -/
theorem selected_signed_atom_negative_573 (i formula move : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (htag : (Cantor.unpair formula).1 = 0) (htop : base 4 = 0)
    (h : graphSystem.run i = cfgHalf 573 base move formula 0 0 reserve) :
    ∃ duration padding finish, formula+2 ≤ duration ∧ Good finish ∧
      finish.graphState = cfgAtom 724 base (if M236Game.encodedAtom (Cantor.unpair formula).2 (base 5) then 1 else 0)
        0 0 0 0 0 (reserve ++ List.replicate padding 0) ∧
      graphSystem.run (i+duration) = cfgAtom 724 base (if M236Game.encodedAtom (Cantor.unpair formula).2 (base 5) then 1 else 0)
        0 0 0 0 0 (reserve ++ List.replicate padding 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run (graphRefinement.boundary (i+duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i+duration) := by
  exact selected_signed_atom_of_block i formula move 573 (M236Game.encodedAtom (Cantor.unpair formula).2 (base 5))
    base reserve h (signed_atom_negative_573 formula move base reserve htag htop)

/-- Emit all remaining coordinates, emit an arbitrary Boolean payoff and
return to the clean next-stage bank from a prepared residual-loop entry. -/
theorem residual_coordinates_boolean_frame (n : Nat) (base : RegisterMachine.Bank 9) (rest : Nat)
    (reserve : List Nat) (value : Bool) (h0 : base 0 = 0)
    (h4 : base 4 = PASoundness.UnaryCodec.bitNat value) :
    ∃ duration padding, n+7 ≤ duration ∧
      graphSystem.Block (cfgRAC 726 (bankOnlyCount base n) rest 0 0 reserve) duration
        (cfg 0 BlankFirst.zeros (base 1+1) 0 0 (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.encodeFields (Schedule.decodeCoordinates n rest) ++
          PASoundness.UnaryCodec.unary (PASoundness.UnaryCodec.bitNat value)) := by
  obtain ⟨duration, padding, hd, hresidual⟩ := residual_coordinates_finish n base rest reserve h0
  let bank := bankAC (bankRest (bankOnlyCount base 0) (residualTail n rest)) 0 0
  have hb0 : bank 0 = 0 := by simp [bank, bankAC, bankRest, bankOnlyCount, h0]
  have hb3 : bank 3 = 0 := by simp [bank, bankAC, bankRest, bankOnlyCount]
  have hb4 : bank 4 = PASoundness.UnaryCodec.bitNat value := by simp [bank, bankAC, bankRest, bankOnlyCount, h4]
  have hb6 : bank 6 = 0 := by simp [bank, bankAC]
  have hb8 : bank 8 = 0 := by simp [bank, bankAC]
  have hb1 : bank 1 = base 1 := by simp [bank, bankAC, bankRest, bankOnlyCount]
  have hclean := final_cleanup bank (bank 2) (bank 5) (bank 7) (bank 4) (reserve ++ List.replicate padding 0)
  rw [← final_cfg_view 749 bank (reserve ++ List.replicate padding 0)] at hclean
  have hbank : RegisterMachine.write (finalBank bank 0 0 0 0) 1 (bank 1+1) =
      bankWith BlankFirst.zeros (bank 1+1) 0 0 := by
    funext i
    fin_cases i <;> simp [finalBank, RegisterMachine.write, bankWith, BlankFirst.zeros, hb0, hb3, hb6, hb8]
  rw [hbank, hb4] at hclean
  have hword : List.replicate (PASoundness.UnaryCodec.bitNat value) true ++ [false] =
      PASoundness.UnaryCodec.unary (PASoundness.UnaryCodec.bitNat value) := by
    cases value <;> rfl
  rw [hword] at hclean
  have hentry : cfgRAC 749 (bankOnlyCount base 0) (residualTail n rest) 0 0
      (reserve ++ List.replicate padding 0) = cfgExact 749 bank (reserve ++ List.replicate padding 0) := rfl
  rw [hentry] at hresidual
  have h := hresidual.trans graphSystem hclean
  refine ⟨duration + (2*(bank 2+bank 5+bank 7)+3*PASoundness.UnaryCodec.bitNat value+6),
    padding + (bank 2+bank 5+bank 7+PASoundness.UnaryCodec.bitNat value), by omega, ?_⟩
  have hreserve : (reserve ++ List.replicate padding 0) ++
      List.replicate (bank 2+bank 5+bank 7+PASoundness.UnaryCodec.bitNat value) 0 =
        reserve ++ List.replicate (padding+(bank 2+bank 5+bank 7+PASoundness.UnaryCodec.bitNat value)) 0 := by
    simp only [List.replicate_add, List.append_assoc]
  rw [hreserve, hb1] at h
  simpa [cfg, cfgExact] using h

/-- From a computed Boolean payoff at entry 724, finish the remaining
coordinates, emit the Boolean field and return to a clean scheduler boundary. -/
theorem atomic_payoff_finish (base : RegisterMachine.Bank 9) (value : Bool) (reserve : List Nat) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block (cfgAtom 724 base (PASoundness.UnaryCodec.bitNat value) 0 0 0 0 0 reserve) duration
        (cfg 0 BlankFirst.zeros (base 1+1) 0 0 (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.encodeFields (Schedule.decodeCoordinates (base 3) (base 2)) ++
          PASoundness.UnaryCodec.unary (PASoundness.UnaryCodec.bitNat value)) := by
  let bank := (cfgAtom 724 base (PASoundness.UnaryCodec.bitNat value) 0 0 0 0 0 reserve).registers
  have hstart : cfgAtom 724 base (PASoundness.UnaryCodec.bitNat value) 0 0 0 0 0 reserve =
      cfgAS 724 bank 0 0 reserve := by
    unfold cfgAtom cfgEnv cfgHalf cfgAS
    congr 1
    funext i
    fin_cases i <;> simp [bank, cfgAtom, cfgEnv, cfgHalf, bankAS, bankHalf, RegisterMachine.write]
  have hb8 : bank 8 = 0 := by simp [bank, cfgAtom, cfgEnv, cfgHalf, bankHalf]
  have hb3 : bank 3 = base 3 := by simp [bank, cfgAtom, cfgEnv, cfgHalf, bankHalf, RegisterMachine.write]
  have hb2 : bank 2 = base 2 := by simp [bank, cfgAtom, cfgEnv, cfgHalf, bankHalf, RegisterMachine.write]
  have hb1 : bank 1 = base 1 := by simp [bank, cfgAtom, cfgEnv, cfgHalf, bankHalf, RegisterMachine.write]
  have hs0 : bankAS bank 0 0 0 = 0 := by simp [bankAS]
  have hs4 : bankAS bank 0 0 4 = PASoundness.UnaryCodec.bitNat value := by
    simp [bank, cfgAtom, cfgEnv, cfgHalf, bankHalf, bankAS, RegisterMachine.write]
  have h1 := residual_entry_drain 0 bank 0 reserve
  rw [← hstart, residual_entry_to_loop bank _ hb8] at h1
  simp only [List.replicate_zero, List.append_nil] at h1
  rw [hb3, hb2] at h1
  obtain ⟨duration, padding, ht, h2⟩ := residual_coordinates_boolean_frame (bank 3) (bankAS bank 0 0) (bank 2)
    reserve value hs0 hs4
  have hb1' : bankAS bank 0 0 1 = base 1 := by simpa [bankAS] using hb1
  rw [hb3, hb2, hb1'] at h2
  refine ⟨1+duration, padding, by omega, ?_⟩
  simpa using h1.trans graphSystem h2

/-- Any checked signed atom block composes with residual-coordinate emission
and Boolean final cleanup into the next clean scheduler boundary. -/
theorem signed_atom_finish_of_block (formula move k : Nat) (output : Bool)
    (base : RegisterMachine.Bank 9) (reserve : List Nat)
    (block : ∃ duration padding, formula+2 ≤ duration ∧
      graphSystem.Block (cfgHalf k base move formula 0 0 reserve) duration
        (cfgAtom 724 base (PASoundness.UnaryCodec.bitNat output) 0 0 0 0 0
          (reserve ++ List.replicate padding 0)) []) :
    ∃ duration padding, formula+2 ≤ duration ∧
      graphSystem.Block (cfgHalf k base move formula 0 0 reserve) duration
        (cfg 0 BlankFirst.zeros (base 1+1) 0 0 (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.encodeFields (Schedule.decodeCoordinates (base 3) (base 2)) ++
          PASoundness.UnaryCodec.unary (PASoundness.UnaryCodec.bitNat output)) := by
  obtain ⟨d1, p1, hd1, h1⟩ := block
  obtain ⟨d2, p2, hd2, h2⟩ := atomic_payoff_finish base output (reserve ++ List.replicate p1 0)
  have h := h1.trans graphSystem h2
  refine ⟨d1+d2, p1+p2, by omega, ?_⟩
  have hr : (reserve ++ List.replicate p1 0) ++ List.replicate p2 0 =
      reserve ++ List.replicate (p1+p2) 0 := by simp only [List.replicate_add, List.append_assoc]
  simp only [List.nil_append] at h
  rw [hr] at h
  exact h

/-- Initial negative atom, including the remaining fields and the final bit. -/
theorem signed_atom_negative_finish_216 (formula move : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (htag : (Cantor.unpair formula).1 = 0) (htop : base 4 = 0) :
    ∃ duration padding, formula+2 ≤ duration ∧
      graphSystem.Block (cfgHalf 216 base move formula 0 0 reserve) duration
        (cfg 0 BlankFirst.zeros (base 1+1) 0 0 (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.encodeFields (Schedule.decodeCoordinates (base 3) (base 2)) ++
          PASoundness.UnaryCodec.unary (PASoundness.UnaryCodec.bitNat
            (M236Game.encodedAtom (Cantor.unpair formula).2 (base 5)))) := by
  apply signed_atom_finish_of_block formula move 216 (M236Game.encodedAtom (Cantor.unpair formula).2 (base 5)) base reserve
  simpa only [PASoundness.UnaryCodec.bitNat] using signed_atom_negative_216 formula move base reserve htag htop

/-- Positive atom, including the remaining fields and complemented final bit. -/
theorem signed_atom_positive_finish_393 (formula move : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (htag : (Cantor.unpair formula).1 = 0) (htop : base 4 = 0) :
    ∃ duration padding, formula+2 ≤ duration ∧
      graphSystem.Block (cfgHalf 393 base move formula 0 0 reserve) duration
        (cfg 0 BlankFirst.zeros (base 1+1) 0 0 (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.encodeFields (Schedule.decodeCoordinates (base 3) (base 2)) ++
          PASoundness.UnaryCodec.unary (PASoundness.UnaryCodec.bitNat
            (!M236Game.encodedAtom (Cantor.unpair formula).2 (base 5)))) := by
  apply signed_atom_finish_of_block formula move 393 (!M236Game.encodedAtom (Cantor.unpair formula).2 (base 5)) base reserve
  simpa only [PASoundness.UnaryCodec.bitNat] using signed_atom_positive_393 formula move base reserve htag htop

/-- Recurring negative atom, including the remaining fields and final bit. -/
theorem signed_atom_negative_finish_573 (formula move : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (htag : (Cantor.unpair formula).1 = 0) (htop : base 4 = 0) :
    ∃ duration padding, formula+2 ≤ duration ∧
      graphSystem.Block (cfgHalf 573 base move formula 0 0 reserve) duration
        (cfg 0 BlankFirst.zeros (base 1+1) 0 0 (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.encodeFields (Schedule.decodeCoordinates (base 3) (base 2)) ++
          PASoundness.UnaryCodec.unary (PASoundness.UnaryCodec.bitNat
            (M236Game.encodedAtom (Cantor.unpair formula).2 (base 5)))) := by
  apply signed_atom_finish_of_block formula move 573 (M236Game.encodedAtom (Cantor.unpair formula).2 (base 5)) base reserve
  simpa only [PASoundness.UnaryCodec.bitNat] using signed_atom_negative_573 formula move base reserve htag htop

/-- A signed-atom completion block lifts to the physical run at a reached
prepared formula-scan entry, preserving the full emitted suffix. -/
theorem selected_signed_atom_finish_of_block (i formula move k : Nat) (output : Bool)
    (base : RegisterMachine.Bank 9) (reserve : List Nat)
    (h : graphSystem.run i = cfgHalf k base move formula 0 0 reserve)
    (block : ∃ duration padding, formula+2 ≤ duration ∧
      graphSystem.Block (cfgHalf k base move formula 0 0 reserve) duration
        (cfg 0 BlankFirst.zeros (base 1+1) 0 0 (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.encodeFields (Schedule.decodeCoordinates (base 3) (base 2)) ++
          PASoundness.UnaryCodec.unary (PASoundness.UnaryCodec.bitNat output))) :
    ∃ duration padding finish, formula+2 ≤ duration ∧ Good finish ∧
      finish.graphState = cfg 0 BlankFirst.zeros (base 1+1) 0 0 (reserve ++ List.replicate padding 0) ∧
      graphSystem.run (i+duration) = cfg 0 BlankFirst.zeros (base 1+1) 0 0 (reserve ++ List.replicate padding 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i+duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++
          (PASoundness.UnaryCodec.encodeFields (Schedule.decodeCoordinates (base 3) (base 2)) ++
            PASoundness.UnaryCodec.unary (PASoundness.UnaryCodec.bitNat output)) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i+duration) := by
  obtain ⟨duration, padding, ht, hb⟩ := block
  have hr : graphSystem.run (i+duration) = cfg 0 BlankFirst.zeros (base 1+1) 0 0
      (reserve ++ List.replicate padding 0) := by
    rw [WordEventSystem.run_add, h, hb.endpoint]
  have hp : graphSystem.prefixWord (i+duration) = graphSystem.prefixWord i ++
      (PASoundness.UnaryCodec.encodeFields (Schedule.decodeCoordinates (base 3) (base 2)) ++
        PASoundness.UnaryCodec.unary (PASoundness.UnaryCodec.bitNat output)) := by
    rw [WordEventSystem.prefix_add, h, hb.output]
  obtain ⟨finish, hg, hs, hconfig⟩ := graphRefinement.related (i+duration)
  refine ⟨duration, padding, finish, ht, hg, hs.trans hr, hr, hconfig, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

end PASoundness.M236.OccurrenceGraph
