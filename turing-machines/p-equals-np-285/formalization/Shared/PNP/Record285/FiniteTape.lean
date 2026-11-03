import Shared.Codes.FinitePrograms
import Shared.PNP.Record285.CanonicalInput

/-! Full-tape relation between the shared finite-program evaluator's lists and
an integer-indexed binary tape. Missing list cells are blank. -/
namespace Shared.PNP.Record285.FiniteTape
open Shared.PNP.Record285.RelativeTape
open Shared.PNP.Record285.CanonicalInput

abbrev Tape := Shared.Codes.FinitePrograms.Tape

def Rel (t : Tape) (tape : Int → Bool) (head : Int) : Prop :=
  tape head = t.2.1 ∧
  (∀ i : Nat, tape (head - (i : Int) - 1) = t.1[i]?.getD false) ∧
  (∀ i : Nat, tape (head + (i : Int) + 1) = t.2.2[i]?.getD false)

def writeAt (tape : Int → Bool) (head : Int) (b : Bool) : Int → Bool :=
  fun pos => if pos = head then b else tape pos

/-- A finite-program move preserves every cell of the blank-padded tape. -/
theorem move_rel (t : Tape) (tape : Int → Bool) (head : Int) (write left : Bool)
    (h : Rel t tape head) :
    Rel (Shared.Codes.FinitePrograms.moveTape left write t) (writeAt tape head write)
      (head + if left then -1 else 1) := by
  rcases t with ⟨L,b,R⟩
  rcases h with ⟨hh,hl,hr⟩
  cases left with
  | false =>
    simp only [Shared.Codes.FinitePrograms.moveTape, Bool.false_eq_true, if_false, Rel]
    constructor
    · have hne : head + 1 ≠ head := by omega
      simp only [writeAt, hne, if_false]
      simpa [List.head?_eq_getElem?] using hr 0
    constructor
    · intro i
      cases i with
      | zero => simp [writeAt]
      | succ i =>
        have hne : head + 1 - (↑(i+1) : Int) - 1 ≠ head := by omega
        simp only [writeAt, hne, if_false, List.getElem?_cons_succ]
        have hp : head + 1 - (↑(i+1) : Int) - 1 = head - (↑i : Int) - 1 := by omega
        rw [hp]
        exact hl i
    · intro i
      have hne : head + 1 + (↑i : Int) + 1 ≠ head := by omega
      simp only [writeAt, hne, if_false, List.getElem?_tail]
      have hp : head + 1 + (↑i : Int) + 1 = head + (↑(i+1) : Int) + 1 := by omega
      rw [hp]
      exact hr (i+1)
  | true =>
    simp only [Shared.Codes.FinitePrograms.moveTape, if_true, Rel]
    constructor
    · have hne : head + -1 ≠ head := by omega
      simp only [writeAt, hne, if_false]
      simpa [List.head?_eq_getElem?, Int.sub_eq_add_neg] using hl 0
    constructor
    · intro i
      have hne : head + -1 - (↑i : Int) - 1 ≠ head := by omega
      simp only [writeAt, hne, if_false, List.getElem?_tail]
      have hp : head + -1 - (↑i : Int) - 1 = head - (↑(i+1) : Int) - 1 := by omega
      rw [hp]
      exact hl (i+1)
    · intro i
      cases i with
      | zero => simp [writeAt]
      | succ i =>
        have hne : head + -1 + (↑(i+1) : Int) + 1 ≠ head := by omega
        simp only [writeAt, hne, if_false, List.getElem?_cons_succ]
        have hp : head + -1 + (↑(i+1) : Int) + 1 = head + (↑i : Int) + 1 := by omega
        rw [hp]
        exact hr i

/-- The finite-program initial lists describe precisely the same entire tape
as the source's low-endian numeric input, including every blank suffix cell. -/
theorem initial_rel (word : List Bool) :
    Rel (Shared.Codes.FinitePrograms.initial word).2 (inputTape (value word)) 0 := by
  constructor
  · cases word with
    | nil => rfl
    | cons b bs => simpa [Shared.Codes.FinitePrograms.initial, inputTape, value_bit] using value_bit (b::bs) 0
  constructor
  · intro i
    simp [Shared.Codes.FinitePrograms.initial, inputTape]; omega
  · intro i
    have hn : (0 : Int) ≤ 0 + (↑i : Int) + 1 := by omega
    have hnat : (0 + (↑i : Int) + 1).toNat = i+1 := by omega
    simp only [inputTape, hn, if_true, hnat, value_bit]
    cases word <;> simp [Shared.Codes.FinitePrograms.initial]

end Shared.PNP.Record285.FiniteTape
