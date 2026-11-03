import Shared.Codes.FinitePrograms
import Shared.ComplexityBridge.CircuitTable
import Shared.Codes.FiniteProgramUntag

/-! Reflect a finite binary table across the head. This is an exact-step
simulation of the result-tagged finite-program model. -/
namespace Shared.Codes.FiniteProgramMirror
open Shared.Codes.FinitePrograms

def tape (t : Tape) : Tape := (t.2.2,t.2.1,t.1)
def config (c : Config) : Config := (c.1,tape c.2)
def status : Status → Status
  | none => none
  | some (.inl b) => some (.inl b)
  | some (.inr c) => some (.inr (config c))

def row (r : Row) : Row := (r.1,!r.2.1,r.2.2.1,r.2.2.2)
def pair (r : Row × Row) : Row × Row := (row r.1,row r.2)
def program (p : Program) : Program := p.map pair

@[simp] theorem program_length (p : Program) : (program p).length = p.length := by simp [program]

@[simp] theorem tape_involutive (t : Tape) : tape (tape t) = t := by cases t with | mk l r => cases r; rfl
@[simp] theorem config_involutive (c : Config) : config (config c) = c := by cases c; simp [config]

theorem move (dir written : Bool) (t : Tape) :
    tape (moveTape dir written t) = moveTape (!dir) written (tape t) := by
  cases dir <;> rfl

theorem execute (r : Row) (t : Tape) :
    executeRow (row r) (tape t) = status (executeRow r t) := by
  rcases r with ⟨w,dir,q,tag⟩
  cases tag with
  | zero => simp [executeRow,row,status,config,move]
  | succ tag => cases tag with
    | zero => rfl
    | succ tag => cases tag with
      | zero => rfl
      | succ tag => rfl

theorem step_mirror (p : Program) (c : Config) :
    step (program p) (config c) = status (step p c) := by
  cases hp : p[c.1]? with
  | none => simp [step,program,config,hp,status]
  | some rows =>
    have he : (program p)[c.1]? = some (pair rows) := by simp [program,hp]
    cases hb : c.2.2.1 with
    | false =>
      have h₁ : rowAt p c = some rows.1 := by simp [rowAt,hp,hb]
      have h₂ : rowAt (program p) (config c) = some (row rows.1) := by
        simp [rowAt,config,tape,he,hb,pair]
      rw [Shared.ComplexityBridge.CircuitTable.step_eq_executeRow _ _ _ h₁,
        Shared.ComplexityBridge.CircuitTable.step_eq_executeRow _ _ _ h₂]
      exact execute _ _
    | true =>
      have h₁ : rowAt p c = some rows.2 := by simp [rowAt,hp,hb]
      have h₂ : rowAt (program p) (config c) = some (row rows.2) := by
        simp [rowAt,config,tape,he,hb,pair]
      rw [Shared.ComplexityBridge.CircuitTable.step_eq_executeRow _ _ _ h₁,
        Shared.ComplexityBridge.CircuitTable.step_eq_executeRow _ _ _ h₂]
      exact execute _ _

theorem advance_mirror (p : Program) (s : Status) :
    advance (program p) (status s) = status (advance p s) := by
  cases s with
  | none => rfl
  | some v => cases v with
    | inl b => rfl
    | inr c => exact step_mirror p c

theorem run_mirror (p : Program) (c : Config) (n : Nat) :
    run (program p) (config c) n = status (run p c n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run_succ,run_succ,ih,advance_mirror]

theorem valid_mirror (p : Program) : valid (program p) = valid p := by
  simp [valid,program,pair,row,validRow,Function.comp_def]

open Shared.Codes.FiniteProgramBitShuttle (tagged tagged_cons tagged_append)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)

/-- Every three-cell tag is symmetric, so reversal reverses the data order. -/
theorem tagged_reverse (xs : List Bool) : (tagged xs).reverse = tagged xs.reverse := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    simp only [tagged_cons,List.reverse_cons]
    rw [tagged_append]
    rw [ih]
    simp [tagged,List.append_assoc]

/-- Reflected untagging takes exactly the same number of transitions. -/
theorem untag_reflected (xs L R : List Bool) (b : Bool) :
    run (program Shared.Codes.FiniteProgramUntag.program)
      (0,(false::tagged xs ++ false::R,b,L)) (Shared.Codes.FiniteProgramUntag.cost xs) =
      some (.inr (12,(false::false::Shared.Codes.FiniteProgramUntag.padding xs.length R,
        (Shared.Codes.FiniteProgramUntag.cursor b L xs).1,
        (Shared.Codes.FiniteProgramUntag.cursor b L xs).2))) := by
  have h := run_mirror Shared.Codes.FiniteProgramUntag.program
    (0,tapeAt L (b::false::tagged xs ++ false::R)) (Shared.Codes.FiniteProgramUntag.cost xs)
  rw [Shared.Codes.FiniteProgramUntag.run_all] at h
  simpa [config,tape,status,tapeAt,List.cons_append] using h

/-- Start just to the right of the decoder's tagged output, with one blank
separator and one blank source cell. The reflected table unpacks all bits
and leaves the head at the first raw bit; the right tail is preserved. -/
theorem untag_from_right (words L R : List Bool) :
    run (program Shared.Codes.FiniteProgramUntag.program)
      (0,(false::(tagged words).reverse ++ false::false::L,false,R))
      (Shared.Codes.FiniteProgramUntag.cost words.reverse) =
      some (.inr (12,tapeAt
        (false::false::Shared.Codes.FiniteProgramUntag.padding words.length (false::L))
        (words ++ false::R))) := by
  have h := untag_reflected words.reverse R (false::L) false
  have hc := Shared.Codes.FiniteProgramUntag.cursor_contents false R words.reverse
  simp only [List.reverse_reverse] at hc
  rw [tagged_reverse]
  have ht : tapeAt (false::false::Shared.Codes.FiniteProgramUntag.padding words.length (false::L))
      ((Shared.Codes.FiniteProgramUntag.cursor false R words.reverse).1::
       (Shared.Codes.FiniteProgramUntag.cursor false R words.reverse).2) =
      tapeAt (false::false::Shared.Codes.FiniteProgramUntag.padding words.length (false::L)) (words ++ false::R) := by
    rw [hc]
  simp only [List.length_reverse] at h
  change run (program Shared.Codes.FiniteProgramUntag.program) _ _ =
    some (.inr (12,tapeAt (false::false::Shared.Codes.FiniteProgramUntag.padding words.length (false::L))
      ((Shared.Codes.FiniteProgramUntag.cursor false R words.reverse).1::
       (Shared.Codes.FiniteProgramUntag.cursor false R words.reverse).2))) at h
  rw [ht] at h
  exact h

theorem reflected_untag_valid : valid (program Shared.Codes.FiniteProgramUntag.program) = true := by
  rw [valid_mirror]
  exact Shared.Codes.FiniteProgramUntag.program_valid

theorem reflected_untag_length : (program Shared.Codes.FiniteProgramUntag.program).length = 43 := by
  rw [program_length,Shared.Codes.FiniteProgramUntag.program_length]

/-- Move right twice across the two decoder blanks before entering the
reflected untagger. Both transitions preserve their read bits. -/
def entryPre : Program :=
  [ ((false,true,1,0),(true,true,1,0)),
    ((false,true,2,0),(true,true,2,0)) ]

def positioned : Program :=
  Shared.Codes.FiniteProgramLink.link entryPre (program Shared.Codes.FiniteProgramUntag.program) []

theorem positioned_length : positioned.length = 45 := by
  simp [positioned,Shared.Codes.FiniteProgramLink.link,entryPre,Shared.Codes.FiniteProgramUntag.program_length]

theorem positioned_valid : valid positioned = true := by decide

theorem entry (b : Bool) (L R : List Bool) :
    run positioned (0,tapeAt L (b::false::false::R)) 2 =
      some (.inr (2,(false::b::L,false,R))) := by
  cases b <;> simp [positioned,Shared.Codes.FiniteProgramLink.link,entryPre,run,advance,step,tapeAt,moveTape]

/-- The entry table starts at the decoder's cursor, pays for positioning,
and leaves the first untagged bit under the head. When `words` is empty the
head reads blank; no data bit is invented. -/
theorem positioned_run (words L R : List Bool) :
    let c := Shared.Codes.FiniteProgramCrossTag.cursor false (false::L) words
    run positioned (0,tapeAt c.2 (c.1::false::false::R))
      (2+Shared.Codes.FiniteProgramUntag.cost words.reverse) =
      some (.inr (14,tapeAt
        (false::false::Shared.Codes.FiniteProgramUntag.padding words.length (false::L))
        (words ++ false::R))) := by
  dsimp only
  let c := Shared.Codes.FiniteProgramCrossTag.cursor false (false::L) words
  have he := entry c.1 c.2 R
  have hc := Shared.Codes.FiniteProgramCrossTag.cursor_contents false (false::L) words
  change c.1::c.2 = _ at hc
  rw [hc] at he
  have hs := Shared.Codes.FiniteProgramLink.run_shift entryPre
    (program Shared.Codes.FiniteProgramUntag.program) [] reflected_untag_valid
    (0,(false::(tagged words).reverse ++ false::false::L,false,R))
    (by simp [Shared.Codes.FiniteProgramUntag.program_length]) (Shared.Codes.FiniteProgramUntag.cost words.reverse)
  rw [untag_from_right] at hs
  rw [Shared.ComplexityBridge.TM0FiniteProgram.run_continue _ _ _ _ _ he]
  simpa [positioned,entryPre,Shared.Codes.FiniteProgramLink.shiftConfig,
    Shared.Codes.FiniteProgramLink.shiftStatus] using hs

/-- The positioning and conversion cost is quadratic in the number of bits. -/
theorem positioned_cost_bound (words : List Bool) :
    2+Shared.Codes.FiniteProgramUntag.cost words.reverse ≤ words.length*(20*words.length+21)+6 := by
  have h := Shared.Codes.FiniteProgramUntag.cost_bound words.reverse
  simp only [List.length_reverse] at h
  omega

namespace Fixtures
example : positioned.length = 45 := positioned_length
example : valid positioned = true := positioned_valid
example : run positioned (0,tapeAt [] [true,false,false]) 2 =
    some (.inr (2,([false,true],false,[]))) := by decide
example : 2+Shared.Codes.FiniteProgramUntag.cost ([] : List Bool).reverse = 6 := by decide
end Fixtures

end Shared.Codes.FiniteProgramMirror
