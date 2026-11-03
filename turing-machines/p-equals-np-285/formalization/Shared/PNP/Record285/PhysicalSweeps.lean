import Shared.PNP.Record285.BootstrapSweep

/-! Uniform, event-free physical tape sweeps. These lemmas apply to arbitrary
full finite-support tapes and machine rows; they do not assert an initialization
boundary or any source-level machine behavior. -/
namespace Shared.PNP.Record285.PhysicalSweeps
open Shared.Beeping.Machines
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep

/-- For a two-state sweep, the first read is `b`, its neighboring bit is
`!b`, and each further pair repeats those two bits. -/
def pairPattern (b : Bool) : Nat → Bool → Nat → Nat
  | 0,last,tail => bitVal (!b) + 2*bitVal last + 4*tail
  | k+1,last,tail => bitVal (!b) + 2*bitVal b + 4*pairPattern b k last tail

@[simp] theorem pairPattern_low (b : Bool) (k : Nat) (last : Bool) (tail : Nat) :
    (pairPattern b k last tail).testBit 0 = !b := by
  cases b <;> cases k <;> cases last <;>
    simp [pairPattern,bitVal,Nat.testBit_zero] <;> omega

@[simp] theorem pairPattern_zero_read (b last : Bool) (tail : Nat) :
    (pairPattern b 0 last tail / 2).testBit 0 = last := by
  cases b <;> cases last <;> simp [pairPattern,bitVal,Nat.testBit_zero] <;> omega

@[simp] theorem pairPattern_zero_tail (b last : Bool) (tail : Nat) :
    pairPattern b 0 last tail / 4 = tail := by
  cases b <;> cases last <;> simp [pairPattern,bitVal] <;> omega

@[simp] theorem pairPattern_succ_read (b : Bool) (k : Nat) (last : Bool) (tail : Nat) :
    (pairPattern b (k+1) last tail / 2).testBit 0 = b := by
  cases b <;> simp [pairPattern,bitVal,Nat.testBit_zero] <;> omega

@[simp] theorem pairPattern_succ_tail (b : Bool) (k : Nat) (last : Bool) (tail : Nat) :
    pairPattern b (k+1) last tail / 4 = pairPattern b k last tail := by
  cases b <;> simp [pairPattern,bitVal] <;> omega

/-- Closed form permits efficient independent checking of long runs. -/
theorem pairPattern_closed (b : Bool) (k : Nat) (last : Bool) (tail : Nat) :
    pairPattern b k last tail =
      (bitVal (!b)+2*bitVal b)*rep4 k +
        4^k*(bitVal (!b)+2*bitVal last+4*tail) := by
  induction k with
  | zero => simp [pairPattern,rep4]
  | succ k ih =>
    simp only [pairPattern, ih, Nat.pow_succ, rep4_succ, Nat.mul_add]
    ac_rfl

/-- Generic left sweep from a validated two-step physical rule. -/
theorem pair_sweep_left (M : Machine 285) (q : Fin 285) (b : Bool) (digit : Nat)
    (pair : ∀ (head : Int) (left right : Nat), left.testBit 0 = !b →
      silent M 2 ⟨q,head,left,b,right⟩ =
        some ⟨q,head-2,left/4,(left/2).testBit 0,4*right+digit⟩)
    (k : Nat) (last : Bool) (tail right : Nat) (head : Int) :
    silent M (2*(k+1)) ⟨q,head,pairPattern b k last tail,b,right⟩ =
      some ⟨q,head-2*(k+1),tail,last,push (k+1) digit right⟩ := by
  induction k generalizing head right with
  | zero =>
    have h := pair head (pairPattern b 0 last tail) right (pairPattern_low b 0 last tail)
    simpa only [pairPattern_zero_read, pairPattern_zero_tail, push, Nat.zero_add, Nat.mul_one,
      Int.natCast_zero, Int.zero_add, Int.mul_one] using h
  | succ k ih =>
    have h := pair head (pairPattern b (k+1) last tail) right (pairPattern_low b (k+1) last tail)
    have hfirst : silent M 2 ⟨q,head,pairPattern b (k+1) last tail,b,right⟩ =
        some ⟨q,head-2,pairPattern b k last tail,b,4*right+digit⟩ := by
      simpa only [pairPattern_succ_read, pairPattern_succ_tail] using h
    rw [show 2*((k+1)+1) = 2+2*(k+1) by omega, silent_add, hfirst]
    simp only [Option.bind_some]
    have hh := ih (4*right+digit) (head-2)
    have he : head-2-2*((k : Int)+1) = head-2*((k : Int)+1+1) := by omega
    simpa only [push, Int.natCast_succ, he] using hh

/-- Right-moving counterpart. -/
theorem pair_sweep_right (M : Machine 285) (q : Fin 285) (b : Bool) (digit : Nat)
    (pair : ∀ (head : Int) (left right : Nat), right.testBit 0 = !b →
      silent M 2 ⟨q,head,left,b,right⟩ =
        some ⟨q,head+2,4*left+digit,(right/2).testBit 0,right/4⟩)
    (k : Nat) (last : Bool) (tail left : Nat) (head : Int) :
    silent M (2*(k+1)) ⟨q,head,left,b,pairPattern b k last tail⟩ =
      some ⟨q,head+2*(k+1),push (k+1) digit left,last,tail⟩ := by
  induction k generalizing head left with
  | zero =>
    have h := pair head left (pairPattern b 0 last tail) (pairPattern_low b 0 last tail)
    simpa only [pairPattern_zero_read, pairPattern_zero_tail, push, Nat.zero_add, Nat.mul_one,
      Int.natCast_zero, Int.zero_add, Int.mul_one] using h
  | succ k ih =>
    have h := pair head left (pairPattern b (k+1) last tail) (pairPattern_low b (k+1) last tail)
    have hfirst : silent M 2 ⟨q,head,left,b,pairPattern b (k+1) last tail⟩ =
        some ⟨q,head+2,4*left+digit,b,pairPattern b k last tail⟩ := by
      simpa only [pairPattern_succ_read, pairPattern_succ_tail] using h
    rw [show 2*((k+1)+1) = 2+2*(k+1) by omega, silent_add, hfirst]
    simp only [Option.bind_some]
    have hh := ih (4*left+digit) (head+2)
    have he : head+2+2*((k : Int)+1) = head+2*((k : Int)+1+1) := by omega
    simpa only [push, Int.natCast_succ, he] using hh

/-- A two-row left-moving cycle supplies the abstract pair rule. -/
theorem pair_left (M : Machine 285) (q p : Fin 285) (b w₀ w₁ : Bool)
    (h₀ : M.table.row q b = ⟨w₀,.left,p,false⟩)
    (h₁ : M.table.row p (!b) = ⟨w₁,.left,q,false⟩)
    (head : Int) (left right : Nat) (hlow : left.testBit 0 = !b) :
    silent M 2 ⟨q,head,left,b,right⟩ =
      some ⟨q,head-2,left/4,(left/2).testBit 0,4*right+2*bitVal w₀+bitVal w₁⟩ := by
  simp [silent, PhysicalNumeric.step, h₀, h₁, hlow, Nat.div_div_eq_div_mul]
  congr 1 <;> omega

/-- A two-row right-moving cycle supplies the corresponding right rule. -/
theorem pair_right (M : Machine 285) (q p : Fin 285) (b w₀ w₁ : Bool)
    (h₀ : M.table.row q b = ⟨w₀,.right,p,false⟩)
    (h₁ : M.table.row p (!b) = ⟨w₁,.right,q,false⟩)
    (head : Int) (left right : Nat) (hlow : right.testBit 0 = !b) :
    silent M 2 ⟨q,head,left,b,right⟩ =
      some ⟨q,head+2,4*left+2*bitVal w₀+bitVal w₁,(right/2).testBit 0,right/4⟩ := by
  simp [silent, PhysicalNumeric.step, h₀, h₁, hlow, Nat.div_div_eq_div_mul]
  congr 1 <;> omega

/-- A run has `k` further copies of its current bit, then `last`. -/
def runPattern (b : Bool) : Nat → Bool → Nat → Nat
  | 0,last,tail => bitVal last + 2*tail
  | k+1,last,tail => bitVal b + 2*runPattern b k last tail

@[simp] theorem runPattern_zero_read (b last : Bool) (tail : Nat) :
    (runPattern b 0 last tail).testBit 0 = last := by
  cases last <;> simp [runPattern,bitVal,Nat.testBit_zero] <;> omega

@[simp] theorem runPattern_zero_tail (b last : Bool) (tail : Nat) :
    runPattern b 0 last tail / 2 = tail := by
  cases last <;> simp [runPattern,bitVal] <;> omega

@[simp] theorem runPattern_succ_read (b : Bool) (k : Nat) (last : Bool) (tail : Nat) :
    (runPattern b (k+1) last tail).testBit 0 = b := by
  cases b <;> simp [runPattern,bitVal,Nat.testBit_zero] <;> omega

@[simp] theorem runPattern_succ_tail (b : Bool) (k : Nat) (last : Bool) (tail : Nat) :
    runPattern b (k+1) last tail / 2 = runPattern b k last tail := by
  cases b <;> simp [runPattern,bitVal] <;> omega

/-- Repeatedly write one bit to the half-tape behind the head. -/
def pushBit : Nat → Bool → Nat → Nat
  | 0,_,value => value
  | k+1,b,value => pushBit k b (2*value+bitVal b)

theorem pushBit_affine (k : Nat) (b : Bool) (value : Nat) :
    pushBit k b (2*value+bitVal b) = 2*pushBit k b value+bitVal b := by
  induction k generalizing value with
  | zero => rfl
  | succ k ih =>
    simp only [pushBit]
    exact ih (2*value+bitVal b)

theorem pushBit_closed (k : Nat) (b : Bool) (value : Nat) :
    pushBit k b value = 2^k*value + bitVal b*(2^k-1) := by
  induction k generalizing value with
  | zero => simp [pushBit]
  | succ k ih =>
    rw [pushBit, pushBit_affine, ih, Nat.pow_succ]
    have hp : 1 ≤ 2^k := Nat.one_le_pow k 2 (by decide)
    have hm : (2^k*2)*value = 2*(2^k*value) := by ac_rfl
    rw [hm]
    cases b <;> simp [bitVal] <;> omega

theorem runPattern_closed (b : Bool) (k : Nat) (last : Bool) (tail : Nat) :
    runPattern b k last tail =
      bitVal b*(2^k-1) + 2^k*(bitVal last+2*tail) := by
  induction k with
  | zero => simp [runPattern]
  | succ k ih =>
    rw [runPattern, ih, Nat.pow_succ]
    have hp : 1 ≤ 2^k := Nat.one_le_pow k 2 (by decide)
    have hm : (2^k*2)*(bitVal last+2*tail) = 2*(2^k*(bitVal last+2*tail)) := by ac_rfl
    rw [hm]
    cases b <;> simp [bitVal] <;> omega

/-- A silent self-loop scans an arbitrary finite run to the left, preserving
the entire unread suffix and writing one bit for each traversed cell. -/
theorem run_sweep_left (M : Machine 285) (q : Fin 285) (b w : Bool)
    (row : M.table.row q b = ⟨w,.left,q,false⟩)
    (k : Nat) (last : Bool) (tail right : Nat) (head : Int) :
    silent M (k+1) ⟨q,head,runPattern b k last tail,b,right⟩ =
      some ⟨q,head-(k+1),tail,last,pushBit (k+1) w right⟩ := by
  induction k generalizing head right with
  | zero =>
    simp only [silent,PhysicalNumeric.step,row,Bool.false_eq_true,if_false,
      runPattern_zero_read,runPattern_zero_tail,pushBit, Int.natCast_zero,
      Int.zero_add]
  | succ k ih =>
    rw [show (k+1)+1 = 1+(k+1) by omega, silent_add]
    have hfirst : silent M 1 ⟨q,head,runPattern b (k+1) last tail,b,right⟩ =
        some ⟨q,head-1,runPattern b k last tail,b,2*right+bitVal w⟩ := by
      simp only [silent,PhysicalNumeric.step,row,Bool.false_eq_true,if_false,
        runPattern_succ_read,runPattern_succ_tail]
    rw [hfirst]
    simp only [Option.bind_some]
    have hh := ih (2*right+bitVal w) (head-1)
    have he : head-1-((k : Int)+1) = head-((k : Int)+1+1) := by omega
    rw [show pushBit (1+(k+1)) w right = pushBit (k+1) w (2*right+bitVal w) by
      rw [show 1+(k+1) = (k+1)+1 by omega]; rfl]
    simpa only [Int.natCast_succ, he] using hh

/-- Right-moving counterpart, with the same exact tape accounting. -/
theorem run_sweep_right (M : Machine 285) (q : Fin 285) (b w : Bool)
    (row : M.table.row q b = ⟨w,.right,q,false⟩)
    (k : Nat) (last : Bool) (tail left : Nat) (head : Int) :
    silent M (k+1) ⟨q,head,left,b,runPattern b k last tail⟩ =
      some ⟨q,head+(k+1),pushBit (k+1) w left,last,tail⟩ := by
  induction k generalizing head left with
  | zero =>
    simp only [silent,PhysicalNumeric.step,row,Bool.false_eq_true,if_false,
      runPattern_zero_read,runPattern_zero_tail,pushBit, Int.natCast_zero,
      Int.zero_add]
  | succ k ih =>
    rw [show (k+1)+1 = 1+(k+1) by omega, silent_add]
    have hfirst : silent M 1 ⟨q,head,left,b,runPattern b (k+1) last tail⟩ =
        some ⟨q,head+1,2*left+bitVal w,b,runPattern b k last tail⟩ := by
      simp only [silent,PhysicalNumeric.step,row,Bool.false_eq_true,if_false,
        runPattern_succ_read,runPattern_succ_tail]
    rw [hfirst]
    simp only [Option.bind_some]
    have hh := ih (2*left+bitVal w) (head+1)
    have he : head+1+((k : Int)+1) = head+((k : Int)+1+1) := by omega
    rw [show pushBit (1+(k+1)) w left = pushBit (k+1) w (2*left+bitVal w) by
      rw [show 1+(k+1) = (k+1)+1 by omega]; rfl]
    simpa only [Int.natCast_succ, he] using hh

end Shared.PNP.Record285.PhysicalSweeps
