import Shared.PNP.Record285.PythonDecoder

/-! Natural-number model of the carry-based unary decoder in the producer's
inlined main loop. This is a manual transcription, not an AST binding. The
Python source's `right -= 1` stays nonnegative on reachable states because
the radix is positive. At radix zero, Lean's natural subtraction saturates
whereas Python integers become negative; no Python equality is asserted for
that unreachable case. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonInlineDecoder
open Shared.PNP.Record285.Source

structure Digits where
  write : Bool
  direction : Bool
  state : Nat
  deriving DecidableEq, Repr

def number (d : Digits) : Nat :=
  (if d.write then 1 else 0) + 2*(if d.direction then 1 else 0) + 4*d.state

/-- The body of the Python nested `if write / if direction` carry. -/
def bump (d : Digits) : Digits :=
  if d.write then
    if d.direction then ⟨false,false,d.state+1⟩ else ⟨false,true,d.state⟩
  else ⟨true,d.direction,d.state⟩

@[simp] theorem bump_number (d : Digits) : number (bump d) = number d + 1 := by
  rcases d with ⟨w,dir,n⟩
  cases w <;> cases dir <;> simp [number,bump] <;> omega

def bumpN : Nat → Digits → Digits
  | 0, d => d
  | n+1, d => bumpN n (bump d)

theorem bumpN_number (n : Nat) (d : Digits) : number (bumpN n d) = number d+n := by
  induction n generalizing d with
  | zero => simp [bumpN]
  | succ n ih => simp [bumpN,ih]; omega

/-- Execute the Python `while digit % 2` loop and its final delimiter
consumption, with the accumulator fields explicitly represented. -/
def read (digit : Nat) (d : Digits) : Digits × Nat :=
  if digit%2=1 then read (digit/2) (bump d) else (d,digit/2)
termination_by digit
decreasing_by omega

theorem read_correct (digit : Nat) (d : Digits) :
    read digit d = (bumpN (popUnary digit).1 d,(popUnary digit).2) := by
  induction digit using Nat.strongRecOn generalizing d with
  | ind digit ih =>
    by_cases h : digit%2=1
    · have hp : 0 < digit := by omega
      rw [read,popUnary]
      simp only [h,↓reduceIte,↓reduceDIte,bumpN]
      exact ih (digit/2) (by omega) (bump d)
    · rw [read,popUnary]
      simp [h,bumpN]

theorem number_write (d : Digits) :
    (if d.write then 1 else 0) = number d%2 := by
  rcases d with ⟨w,dir,n⟩
  cases w <;> cases dir <;> simp [number] <;> omega

theorem number_direction (d : Digits) :
    (if d.direction then 1 else 0) = (number d/2)%2 := by
  rcases d with ⟨w,dir,n⟩
  cases w <;> cases dir <;> simp [number] <;> omega

theorem number_state (d : Digits) : d.state = number d/4 := by
  rcases d with ⟨w,dir,n⟩
  cases w <;> cases dir <;> simp [number] <;> omega

/-- The carry loop's three outputs and consumed tail are exactly the unary
record's binary fields, for every finite digit including zero. -/
theorem read_fields (digit : Nat) :
    let d := (read digit ⟨false,false,0⟩).1
    let packed := (popUnary digit).1
    (if d.write then 1 else 0) = packed%2 ∧
    (if d.direction then 1 else 0) = (packed/2)%2 ∧
    d.state = packed/4 ∧ (read digit ⟨false,false,0⟩).2 = (popUnary digit).2 := by
  have hnum : number (read digit ⟨false,false,0⟩).1 = (popUnary digit).1 := by
    rw [read_correct]
    simp only [Prod.fst]
    rw [bumpN_number]
    simp [number]
  have hw := number_write (read digit ⟨false,false,0⟩).1
  have hd := number_direction (read digit ⟨false,false,0⟩).1
  have hs := number_state (read digit ⟨false,false,0⟩).1
  rw [hnum] at hw hd hs
  exact ⟨hw,hd,hs,by rw [read_correct]⟩

/-- Execute the outer `while state` loop by consuming one unary record in
each iteration; the count of skipped ones is intentionally discarded. -/
def skip : Nat → Nat → Nat
  | 0, digit => digit
  | count+1, digit => skip count (Shared.PNP.Record285.PythonDecoder.pop digit 0).2

theorem skip_correct (count digit : Nat) : skip count digit = skipUnary count digit := by
  induction count generalizing digit with
  | zero => rfl
  | succ count ih =>
    simp [skip,skipUnary,Shared.PNP.Record285.PythonDecoder.pop_correct,ih]

/-- One main-loop virtual step using the explicit carry decoder. The selector
already includes the separately stored scanned bit, as in the source model. -/
def step (program : Nat) (s : SimState) : Option SimState :=
  let digit := skip (s.selector + s.choices%2) program
  let d := (read digit ⟨false,false,0⟩).1
  let left := if d.direction then s.right else s.left
  let right := if d.direction then s.left else s.right
  if d.state=0 then none
  else some ⟨2*left+(if d.write then 1 else 0),right/2,
    d.state-1+2*(right%2),s.choices/2⟩

/-- The carry-based main-loop transition has the same entire virtual
configuration and HALT behavior as the verified source transition. -/
theorem step_correct (program : Nat) (s : SimState) :
    step program s = simStep program s := by
  let digit := skipUnary (s.selector+s.choices%2) program
  let d := (read digit ⟨false,false,0⟩).1
  let packed := (popUnary digit).1
  have hf := read_fields digit
  change (if d.write then 1 else 0) = packed%2 ∧
    (if d.direction then 1 else 0) = (packed/2)%2 ∧
    d.state = packed/4 ∧ _ at hf
  simp only [step,simStep,skip_correct]
  change (if d.state=0 then none else some (⟨
    2*(if d.direction then s.right else s.left)+(if d.write then 1 else 0),
    (if d.direction then s.left else s.right)/2,
    d.state-1+2*((if d.direction then s.left else s.right)%2),s.choices/2⟩ : SimState)) =
    (if packed/4=0 then none else some (⟨
    2*(if (packed/2)%2=0 then s.left else s.right)+packed%2,
    (if (packed/2)%2=0 then s.right else s.left)/2,
    packed/4-1+2*((if (packed/2)%2=0 then s.right else s.left)%2),s.choices/2⟩ : SimState))
  cases hd : d.direction with
  | false =>
    have hzero : (packed/2)%2 = 0 := by simpa [hd] using hf.2.1.symm
    simp [hd,hzero,←hf.1,←hf.2.2.1]
  | true =>
    have hone : (packed/2)%2 = 1 := by simpa [hd] using hf.2.1.symm
    simp [hd,hone,←hf.1,←hf.2.2.1]

/-- Repeat the inline virtual step for the supplied finite clock. -/
def run (program : Nat) : Nat → SimState → Option SimState
  | 0, s => some s
  | clock+1, s =>
      match step program s with
      | none => none
      | some next => run program clock next

theorem run_correct (program clock : Nat) (s : SimState) :
    run program clock s = runSteps program clock s := by
  induction clock generalizing s with
  | zero => rfl
  | succ clock ih =>
    simp only [run,runSteps,step_correct]
    cases simStep program s <;> simp_all

def halted (program clock : Nat) (s : SimState) : Bool :=
  (run program clock s).isNone

theorem halted_correct (program clock : Nat) (s : SimState) :
    halted program clock s = haltedWithin program clock s := by
  apply Bool.eq_iff_iff.mpr
  rw [show halted program clock s = true ↔ run program clock s = none from
    Option.isNone_iff_eq_none,run_correct,←haltedWithin_iff_runSteps]

def search (program clock : Nat) : Nat → Bool
  | 0 => false
  | branches+1 =>
      if halted program clock ⟨0,0,0,branches⟩ then true
      else search program clock branches

theorem search_correct (program clock branches : Nat) :
    search program clock branches = referenceSearch program clock branches := by
  induction branches with
  | zero => rfl
  | succ branches ih => simp [search,referenceSearch,halted_correct,ih]

/-- For the natural-number transcription, every reference branch and the
deterministic candidate in the inline comparison produce the same mismatch
bit as the abstract source. This theorem includes Lean's saturated zero-radix
case; the actual Python zero-radix behavior is not represented. -/
theorem comparison_correct (program exponent n radix remaining : Nat) :
    (search (radix+remaining) n radix !=
      halted program ((n+2)^exponent)
        ⟨0,(frame radix remaining)/2,2*((frame radix remaining)%2),0⟩) =
      mismatch program exponent n radix remaining := by
  simp [search_correct,halted_correct,mismatch,reference,candidate]

end Shared.PNP.Record285.PythonInlineDecoder
