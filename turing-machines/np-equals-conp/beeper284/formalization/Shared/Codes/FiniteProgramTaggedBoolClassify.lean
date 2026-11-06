import Shared.Codes.FiniteProgramTaggedLoop

/-! A finite-table classifier for the length-sensitive tagged Boolean output.
The three result states are live placeholders for later linking, not halts. -/
namespace Shared.Codes.FiniteProgramTaggedBoolClassify
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramBitShuttle (tagged)
open Shared.Codes.FiniteProgramTaggedLoop (canonical)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)

/-- States 8, 9, and 10 are, respectively, invalid, false, and true exits.
All table rows preserve the scanned bit and move one cell to the right. -/
def program : Program :=
  [ ((false,true,1,0),(true,true,1,0)),
    ((false,true,2,0),(true,true,2,0)),
    ((false,true,8,0),(true,true,3,0)),
    ((false,true,4,0),(true,true,5,0)),
    ((false,true,8,0),(true,true,6,0)),
    ((false,true,8,0),(true,true,7,0)),
    ((false,true,9,0),(true,true,8,0)),
    ((false,true,10,0),(true,true,8,0)),
    ((false,true,8,0),(true,true,8,0)),
    ((false,true,9,0),(true,true,9,0)),
    ((false,true,10,0),(true,true,10,0)) ]

theorem program_valid : valid program = true := by decide
@[simp] theorem program_length : program.length = 11 := rfl

/-- Placeholder rows continue rather than return a Boolean result. -/
theorem invalid_placeholder (t : Tape) :
    step program (8,t) = some (.inr (8,moveTape false t.2.1 t)) := by
  cases h : t.2.1 <;> simp [program,step,h]
theorem false_placeholder (t : Tape) :
    step program (9,t) = some (.inr (9,moveTape false t.2.1 t)) := by
  cases h : t.2.1 <;> simp [program,step,h]
theorem true_placeholder (t : Tape) :
    step program (10,t) = some (.inr (10,moveTape false t.2.1 t)) := by
  cases h : t.2.1 <;> simp [program,step,h]

/-- Only literal one-bit outputs are Boolean results. -/
def resultState : List Bool → Nat
  | [false] => 9
  | [true] => 10
  | _ => 8

/-- The empty buffer is detected after three steps; all others take six. -/
def cost : List Bool → Nat
  | [] => 3
  | _ :: _ => 6

@[simp] theorem cost_empty : cost [] = 3 := rfl
@[simp] theorem cost_nonempty (b : Bool) (xs : List Bool) : cost (b::xs) = 6 := rfl
theorem cost_positive (xs : List Bool) : 0 < cost xs := by cases xs <;> simp [cost]
theorem cost_at_most_six (xs : List Bool) : cost xs ≤ 6 := by cases xs <;> simp [cost]

@[simp] theorem result_false_iff (xs : List Bool) : resultState xs = 9 ↔ xs = [false] := by
  cases xs with
  | nil => decide
  | cons b xs => cases b <;> cases xs <;> simp [resultState]

@[simp] theorem result_true_iff (xs : List Bool) : resultState xs = 10 ↔ xs = [true] := by
  cases xs with
  | nil => decide
  | cons b xs => cases b <;> cases xs <;> simp [resultState]

theorem result_invalid_iff (xs : List Bool) :
    resultState xs = 8 ↔ xs ≠ [false] ∧ xs ≠ [true] := by
  cases xs with
  | nil => simp [resultState]
  | cons b xs => cases b <;> cases xs <;> simp [resultState]

/-- The final tape retains every cell; the head has moved right by `cost`.
Trailing explicit blank cells can be forgotten under `TapeRel`. -/
def inputWord (xs : List Bool) : List Bool :=
  false :: false :: tagged xs ++ [false,false,false]

def finalTape (xs : List Bool) : Tape :=
  tapeAt ((inputWord xs).take (cost xs)).reverse ((inputWord xs).drop (cost xs))

/-- The literal table reaches the right live exit after exactly the stated
positive number of transitions, without altering the represented tape. -/
theorem run_canonical (xs : List Bool) :
    run program (canonical [] false xs) (cost xs) =
      some (.inr (resultState xs,finalTape xs)) := by
  cases xs with
  | nil => simp [program,run,advance,step,canonical,cost,resultState,finalTape,
      inputWord,tagged,tapeAt,moveTape]
  | cons b xs =>
    cases b <;> cases xs <;>
      simp [program,run,advance,step,canonical,cost,resultState,finalTape,
        inputWord,tagged,tapeAt,moveTape]

/-- Classification works on every representation of the canonical tape modulo
trailing blanks, and preserves the related final-tape representation. -/
theorem run_classify_related (xs : List Bool) (c : Config) (hq : c.1 = 0)
    (ht : TapeRel c.2 (canonical [] false xs).2) :
    ∃ t, run program c (cost xs) = some (.inr (resultState xs,t)) ∧
      TapeRel t (finalTape xs) := by
  have h := run_related program c (canonical [] false xs)
    (by simpa [canonical] using hq) ht (cost xs)
  rw [run_canonical xs] at h
  cases hr : run program c (cost xs) with
  | none => simp [StatusRel,hr] at h
  | some v => cases v with
    | inl b => simp [StatusRel,hr] at h
    | inr d =>
      rcases d with ⟨q,t⟩
      rw [hr] at h
      change q = resultState xs ∧ TapeRel t (finalTape xs) at h
      refine ⟨t,?_,h.2⟩
      rw [h.1]

theorem run_classify (xs : List Bool) (c : Config) (hq : c.1 = 0)
    (ht : TapeRel c.2 (canonical [] false xs).2) :
    ∃ t, run program c (cost xs) = some (.inr (resultState xs,t)) := by
  obtain ⟨t,h,_⟩ := run_classify_related xs c hq ht
  exact ⟨t,h⟩

end Shared.Codes.FiniteProgramTaggedBoolClassify
