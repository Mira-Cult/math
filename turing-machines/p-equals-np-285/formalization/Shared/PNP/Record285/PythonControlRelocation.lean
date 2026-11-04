import Shared.PNP.Record285.PythonControlEvaluator

/-! Finite certificate for the shared reference/candidate decoder and action
region. It checks row contents and every syntactic branch target; it is not
by itself an unbounded interpreter simulation. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlRelocation
open Shared.PNP.Record285.PythonSyntax
open Shared.PNP.Record285.PythonControl

/-- Remove the four spaces by which the reference copy is more deeply nested. -/
def unindent : Line → Line
  | .while_ i e => .while_ (i-4) e
  | .if_ i e => .if_ (i-4) e
  | .else_ i => .else_ (i-4)
  | .assign i n e => .assign (i-4) n e
  | .assignMany i ns es => .assignMany (i-4) ns es
  | .aug i n o e => .aug (i-4) n o e
  | .call i n => .call (i-4) n
  | .return_ i e => .return_ (i-4) e
  | .break_ i => .break_ (i-4)
  | line => line

def rowCheck (i : Nat) : Bool :=
  decide ((code[47+i]?).map unindent = code[94+i]?)

def edgeCheck (i : Nat) : Bool :=
  match code[47+i]? with
  | some (.while_ level _) =>
      decide (seek code (48+i) level + 47 = seek code (95+i) (level-4))
  | some (.if_ level _) =>
      decide (jumpFalse code (47+i) level + 47 = jumpFalse code (94+i) (level-4))
  | some (.else_ level) =>
      decide (seek code (48+i) level + 47 = seek code (95+i) (level-4))
  | _ => true

def checks : Bool := (List.range 32).all rowCheck && (List.range 30).all edgeCheck

theorem checks_pass : checks = true := by decide

/-- Every corresponding reference/candidate row has the same typed operation
and operands after the fixed indentation translation. -/
theorem rows_match (i : Nat) (hi : i < 32) :
    (code[47+i]?).map unindent = code[94+i]? := by
  have hall := (Bool.and_eq_true_iff.mp checks_pass).1
  have hr : rowCheck i = true := (List.all_eq_true).1 hall i (List.mem_range.2 hi)
  exact of_decide_eq_true hr

/-- Every applicable while, if and else edge before the distinct terminal
branches has the same fixed address displacement. -/
theorem edges_match (i : Nat) (hi : i < 30) : edgeCheck i = true := by
  have hall := (Bool.and_eq_true_iff.mp checks_pass).2
  exact (List.all_eq_true).1 hall i (List.mem_range.2 hi)

/-- The shared `else` header exits to different surrounding clock loops;
the two addresses differ by 49, not by the internal displacement 47. -/
theorem terminal_exits : seek code 78 20 = 82 ∧ seek code 125 16 = 131 := by decide

/-- The surrounding reference branch loop has one extra frame, so it cannot
be translated by blindly adding 47 to every enclosing loop address. -/
def referenceBase : List Loop := [⟨41,82⟩,⟨34,82⟩,⟨31,140⟩,⟨28,146⟩]
def candidateBase : List Loop := [⟨91,131⟩,⟨31,140⟩,⟨28,146⟩]

def shiftLoop (l : Loop) : Loop := ⟨l.head+47,l.exit+47⟩

/-- Paired dedent processing preserves the fixed displacement for any
nested inner frames whose heads stay inside the common decoder region, while
retaining each evaluator's distinct surrounding loop stack. -/
theorem settle_shared (pc : Nat) (inner : List Loop)
    (hlo : 47 ≤ pc) (hhi : pc ≤ 65)
    (hheads : ∀ l ∈ inner, 47 ≤ l.head ∧ l.head ≤ 65) :
    ∃ target remaining, 47 ≤ target ∧ target ≤ 65 ∧
      settle pc (inner ++ referenceBase) = (target,remaining ++ referenceBase) ∧
      settle (pc+47) (inner.map shiftLoop ++ candidateBase) =
        (target+47,remaining.map shiftLoop ++ candidateBase) := by
  induction inner generalizing pc with
  | nil =>
    refine ⟨pc,[],hlo,hhi,?_,?_⟩ <;>
      simp [settle,referenceBase,candidateBase] <;> omega
  | cons l rest ih =>
    have hl : 47 ≤ l.head ∧ l.head ≤ 65 := hheads l (by simp)
    have hr : ∀ x ∈ rest, 47 ≤ x.head ∧ x.head ≤ 65 := by
      intro x hx
      exact hheads x (by simp [hx])
    by_cases h : l.exit ≤ pc
    · have hc : (shiftLoop l).exit ≤ pc+47 := by simp [shiftLoop]; omega
      obtain ⟨target,remaining,htlo,hthi,href,hcand⟩ := ih l.head hl.1 hl.2 hr
      refine ⟨target,remaining,htlo,hthi,?_,?_⟩
      · simpa [settle,h] using href
      · simpa [settle,h,hc,shiftLoop] using hcand
    · have hc : ¬ (shiftLoop l).exit ≤ pc+47 := by simp [shiftLoop]; omega
      refine ⟨pc,l::rest,hlo,hhi,?_,?_⟩
      · simp [settle,h]
      · simp [settle,h,hc,shiftLoop]

/-- Indentation changes do not alter the complete-store effect or failure
behavior of any straight-line operation. -/
theorem simple_unindent (line : Line) (s : Shared.PNP.Record285.PythonStraight.Store) :
    Shared.PNP.Record285.PythonStraight.simple (unindent line) s =
      Shared.PNP.Record285.PythonStraight.simple line s := by
  cases line <;> rfl

/-- The reference and candidate typed operations share their guard expression
and simultaneous-assignment operands; the verifier checks the exact rows. -/
theorem common_decoder_rows (i : Nat) (hi : i < 18) :
    (code[47+i]?).map unindent = code[94+i]? ∧ edgeCheck i = true := by
  exact ⟨rows_match i (by omega),edges_match i (by omega)⟩

end Shared.PNP.Record285.PythonControlRelocation
