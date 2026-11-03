import Shared.PNP.Record285.BootstrapRows

/-! Silent arithmetic sweeps for the literal record's first bootstrap. These
lemmas describe unbounded families of physical steps, conditional on the ten
bootstrap rows. They are not yet a blank-entry certificate. -/
namespace Shared.PNP.Record285.BootstrapSweep
open Shared.Beeping
open Shared.Beeping.Machines
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapRows

/-- Execute exactly `fuel` numeric transitions, rejecting any marked event. -/
def silent (M : Machine n) : Nat → PhysicalNumeric.Config n → Option (PhysicalNumeric.Config n)
  | 0,c => some c
  | fuel+1,c =>
    let next := PhysicalNumeric.step M c
    if next.2 then none else silent M fuel next.1

theorem silent_add (M : Machine n) (a b : Nat) (c : PhysicalNumeric.Config n) :
    silent M (a+b) c = (silent M a c).bind (silent M b) := by
  induction a generalizing c with
  | zero => simp [silent]
  | succ a ih =>
    simp only [Nat.succ_add, silent]
    cases (PhysicalNumeric.step M c).2 <;> simp [ih]

/-- A successful silent evaluation is an exact-duration numeric run
with no transition events. -/
theorem silent_correct (M : Machine n) (c : PhysicalNumeric.Config n)
    (fuel : Nat) (d : PhysicalNumeric.Config n) (h : silent M fuel c = some d) :
    d = (EventSystem.mk c (PhysicalNumeric.step M)).run fuel ∧
      ∀ t, t < fuel → ¬ (EventSystem.mk c (PhysicalNumeric.step M)).BeepAt t := by
  induction fuel generalizing d with
  | zero =>
    simp only [silent, Option.some.injEq] at h
    subst d
    exact ⟨rfl, by intro t ht; omega⟩
  | succ fuel ih =>
    rw [show fuel+1 = fuel+1 by rfl, silent_add] at h
    cases hp : silent M fuel c with
    | none => simp [hp] at h
    | some previous =>
      obtain ⟨heq,hsilent⟩ := ih previous hp
      simp only [hp, Option.bind_some] at h
      cases hb : (PhysicalNumeric.step M previous).2 with
      | true => simp [silent,hb] at h
      | false =>
        have hnext : (PhysicalNumeric.step M previous).1 = d := by simpa [silent,hb] using h
        constructor
        · rw [EventSystem.run_succ, ← heq]
          exact hnext.symm
        · intro t ht hevent
          by_cases he : t = fuel
          · subst t
            change (PhysicalNumeric.step M ((EventSystem.mk c (PhysicalNumeric.step M)).run fuel)).2 = true at hevent
            rw [← heq,hb] at hevent
            contradiction
          · exact hsilent t (by omega) hevent

/-- Transfer the exact silent segment to a related physical machine, including
its entire two-way tape and absolute head position. -/
theorem silent_physical (M : Machine n) (c : PhysicalNumeric.Config n)
    (physical : Shared.Beeping.Machines.Config n) (hrel : Rel c physical)
    (fuel : Nat) (d : PhysicalNumeric.Config n) (h : silent M fuel c = some d) :
    Rel d ((EventSystem.mk physical M.step).run fuel) ∧
      ∀ t, t < fuel → ¬ (EventSystem.mk physical M.step).BeepAt t := by
  obtain ⟨hd,hsilent⟩ := silent_correct M c fuel d h
  constructor
  · rw [hd]
    exact run_from_related M c physical hrel fuel
  · intro t ht he
    exact hsilent t ht ((beep_from_iff M c physical hrel t).2 he)

/-- A1,C0 moves left two cells and writes two ones. -/
theorem pair_A (M : Machine 285) (rows : Rows M) (head : Int) (left right : Nat)
    (hlow : left.testBit 0 = false) :
    silent M 2 ⟨A,head,left,true,right⟩ =
      some ⟨A,head-2,left/4,(left/2).testBit 0,4*right+3⟩ := by
  simp [silent, PhysicalNumeric.step, rows.A1, rows.C0, hlow, bitVal,
    Nat.div_div_eq_div_mul]
  congr 1 <;> omega

/-- B1,D0 moves left two cells and writes zero then one. -/
theorem pair_B (M : Machine 285) (rows : Rows M) (head : Int) (left right : Nat)
    (hlow : left.testBit 0 = false) :
    silent M 2 ⟨B,head,left,true,right⟩ =
      some ⟨B,head-2,left/4,(left/2).testBit 0,4*right+1⟩ := by
  simp [silent, PhysicalNumeric.step, rows.B1, rows.D0, hlow, bitVal,
    Nat.div_div_eq_div_mul]
  congr 1 <;> omega

/-- D1,E0 moves right two cells and leaves the scanned 1/0 pair intact. -/
theorem pair_D (M : Machine 285) (rows : Rows M) (head : Int) (left right : Nat)
    (hlow : right.testBit 0 = false) :
    silent M 2 ⟨D,head,left,true,right⟩ =
      some ⟨D,head+2,4*left+2,(right/2).testBit 0,right/4⟩ := by
  simp [silent, PhysicalNumeric.step, rows.D1, rows.E0, hlow, bitVal,
    Nat.div_div_eq_div_mul]
  congr 1 <;> omega

/-- `pattern k last tail` supplies `k+1` alternating 1/0 pairs. The
first `k` pairs have a following one; `last` is the final new head bit. -/
def pattern : Nat → Bool → Nat → Nat
  | 0, last, tail => 2*bitVal last + 4*tail
  | k+1, last, tail => 2+4*pattern k last tail

@[simp] theorem pattern_low (k : Nat) (last : Bool) (tail : Nat) :
    (pattern k last tail).testBit 0 = false := by
  cases k <;> cases last <;> simp [pattern, bitVal, Nat.testBit_zero] <;> omega

@[simp] theorem pattern_zero_read (last : Bool) (tail : Nat) :
    (pattern 0 last tail / 2).testBit 0 = last := by
  cases last <;> simp [pattern, bitVal, Nat.testBit_zero] <;> omega

@[simp] theorem pattern_zero_tail (last : Bool) (tail : Nat) :
    pattern 0 last tail / 4 = tail := by
  cases last <;> simp [pattern, bitVal] <;> omega

@[simp] theorem pattern_succ_read (k : Nat) (last : Bool) (tail : Nat) :
    (pattern (k+1) last tail / 2).testBit 0 = true := by
  simp [pattern, Nat.testBit_zero] <;> omega

@[simp] theorem pattern_succ_tail (k : Nat) (last : Bool) (tail : Nat) :
    pattern (k+1) last tail / 4 = pattern k last tail := by
  simp [pattern] <;> omega

/-- Repeatedly push a two-bit base-four digit on a finite half-tape. -/
def push : Nat → Nat → Nat → Nat
  | 0, _, value => value
  | k+1, digit, value => push k digit (4*value+digit)

/-- Closed base-four repunit used by the finite bootstrap certificate. -/
def rep4 (k : Nat) : Nat := (4^k-1)/3

theorem pow4_mod_three (k : Nat) : 4^k % 3 = 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ]
    omega

theorem rep4_succ (k : Nat) : rep4 (k+1) = 4*rep4 k+1 := by
  unfold rep4
  rw [Nat.pow_succ]
  have hm := pow4_mod_three k
  have hp : 1 ≤ 4^k := Nat.one_le_pow k 4 (by decide)
  omega

theorem pow4_rep (k : Nat) : 4^k = 3*rep4 k+1 := by
  have hm := pow4_mod_three k
  have hp : 1 ≤ 4^k := Nat.one_le_pow k 4 (by decide)
  unfold rep4
  omega

theorem push_affine (k digit value : Nat) :
    push k digit (4*value+digit) = 4*push k digit value+digit := by
  induction k generalizing value with
  | zero => rfl
  | succ k ih =>
    simp only [push]
    exact ih (4*value+digit)

/-- Efficient closed form for the repeated two-bit push. -/
theorem push_closed (k digit value : Nat) :
    push k digit value = 4^k*value + digit*rep4 k := by
  induction k generalizing value with
  | zero => simp [push,rep4]
  | succ k ih =>
    rw [push, push_affine, ih, Nat.pow_succ, rep4_succ]
    simp only [Nat.mul_add]
    ac_rfl

/-- Efficient closed form for the alternating input segment. -/
theorem pattern_closed (k : Nat) (last : Bool) (tail : Nat) :
    pattern k last tail = 2*rep4 k + 4^k*(2*bitVal last+4*tail) := by
  induction k with
  | zero => simp [pattern,rep4]
  | succ k ih =>
    simp only [pattern, ih, Nat.pow_succ, rep4_succ, Nat.mul_add]
    ac_rfl

/-- A two-step left-moving rule composes over an arbitrarily long alternating
run. Each pair moves left twice and pushes one base-four digit on the right. -/
theorem sweep_left (M : Machine 285) (q : Fin 285) (digit : Nat)
    (pair : ∀ (head : Int) (left right : Nat), left.testBit 0 = false →
      silent M 2 ⟨q,head,left,true,right⟩ =
        some ⟨q,head-2,left/4,(left/2).testBit 0,4*right+digit⟩)
    (k : Nat) (last : Bool) (tail right : Nat) (head : Int) :
    silent M (2*(k+1)) ⟨q,head,pattern k last tail,true,right⟩ =
      some ⟨q,head-2*(k+1),tail,last,push (k+1) digit right⟩ := by
  induction k generalizing head right with
  | zero =>
    have h := pair head (pattern 0 last tail) right (pattern_low 0 last tail)
    simpa only [pattern_zero_read, pattern_zero_tail, push, Nat.zero_add, Nat.mul_one,
      Int.natCast_zero, Int.zero_add, Int.mul_one] using h
  | succ k ih =>
    have h := pair head (pattern (k+1) last tail) right (pattern_low (k+1) last tail)
    have hfirst : silent M 2 ⟨q,head,pattern (k+1) last tail,true,right⟩ =
        some ⟨q,head-2,pattern k last tail,true,4*right+digit⟩ := by simpa only [pattern_succ_read, pattern_succ_tail] using h
    rw [show 2*((k+1)+1) = 2+2*(k+1) by omega, silent_add, hfirst]
    simp only [Option.bind_some]
    have hh := ih (4*right+digit) (head-2)
    have he : head-2-2*((k : Int)+1) = head-2*((k : Int)+1+1) := by omega
    simpa only [push, Int.natCast_succ, he] using hh

/-- Right-moving counterpart of `sweep_left`. -/
theorem sweep_right (M : Machine 285) (q : Fin 285) (digit : Nat)
    (pair : ∀ (head : Int) (left right : Nat), right.testBit 0 = false →
      silent M 2 ⟨q,head,left,true,right⟩ =
        some ⟨q,head+2,4*left+digit,(right/2).testBit 0,right/4⟩)
    (k : Nat) (last : Bool) (tail left : Nat) (head : Int) :
    silent M (2*(k+1)) ⟨q,head,left,true,pattern k last tail⟩ =
      some ⟨q,head+2*(k+1),push (k+1) digit left,last,tail⟩ := by
  induction k generalizing head left with
  | zero =>
    have h := pair head left (pattern 0 last tail) (pattern_low 0 last tail)
    simpa only [pattern_zero_read, pattern_zero_tail, push, Nat.zero_add, Nat.mul_one,
      Int.natCast_zero, Int.zero_add, Int.mul_one] using h
  | succ k ih =>
    have h := pair head left (pattern (k+1) last tail) (pattern_low (k+1) last tail)
    have hfirst : silent M 2 ⟨q,head,left,true,pattern (k+1) last tail⟩ =
        some ⟨q,head+2,4*left+digit,true,pattern k last tail⟩ := by simpa only [pattern_succ_read, pattern_succ_tail] using h
    rw [show 2*((k+1)+1) = 2+2*(k+1) by omega, silent_add, hfirst]
    simp only [Option.bind_some]
    have hh := ih (4*left+digit) (head+2)
    have he : head+2+2*((k : Int)+1) = head+2*((k : Int)+1+1) := by omega
    simpa only [push, Int.natCast_succ, he] using hh

/-- The three physically occurring sweeps, with every marked event excluded. -/
theorem sweep_A (M : Machine 285) (rows : Rows M) (k : Nat) (last : Bool)
    (tail right : Nat) (head : Int) :
    silent M (2*(k+1)) ⟨A,head,pattern k last tail,true,right⟩ =
      some ⟨A,head-2*(k+1),tail,last,push (k+1) 3 right⟩ :=
  sweep_left M A 3 (pair_A M rows) k last tail right head

theorem sweep_B (M : Machine 285) (rows : Rows M) (k : Nat) (last : Bool)
    (tail right : Nat) (head : Int) :
    silent M (2*(k+1)) ⟨B,head,pattern k last tail,true,right⟩ =
      some ⟨B,head-2*(k+1),tail,last,push (k+1) 1 right⟩ :=
  sweep_left M B 1 (pair_B M rows) k last tail right head

theorem sweep_D (M : Machine 285) (rows : Rows M) (k : Nat) (last : Bool)
    (tail left : Nat) (head : Int) :
    silent M (2*(k+1)) ⟨D,head,left,true,pattern k last tail⟩ =
      some ⟨D,head+2*(k+1),push (k+1) 2 left,last,tail⟩ :=
  sweep_right M D 2 (pair_D M rows) k last tail left head

end Shared.PNP.Record285.BootstrapSweep
