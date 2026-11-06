import Shared.Codes.FiniteProgramRepair
import Shared.ComplexityBridge.TM0FiniteProgram
import Shared.Codes.FiniteProgramTapeEquiv

/-! Exact-step relocation of valid finite-program tables behind a prefix.
The tape is unchanged by relocation. This is a linking theorem, not an input
preprocessor or an unbounded-program termination assumption. -/
namespace Shared.Codes.FiniteProgramLink
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge.CircuitTable (step_eq_executeRow)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

/-- Move the numeric destination by the prefix length. Result rows do not
observe their destination field, so shifting it is harmless for every tag. -/
def shiftRow (offset : Nat) (row : Row) : Row :=
  (row.1,row.2.1,offset+row.2.2.1,row.2.2.2)

def shiftPair (offset : Nat) (rows : Row × Row) : Row × Row :=
  (shiftRow offset rows.1,shiftRow offset rows.2)

def link (pre p suffix : Program) : Program :=
  pre ++ p.map (shiftPair pre.length) ++ suffix

def shiftConfig (offset : Nat) (c : Config) : Config := (offset+c.1,c.2)

def shiftStatus (offset : Nat) : Status → Status
  | none => none
  | some (.inl b) => some (.inl b)
  | some (.inr c) => some (.inr (shiftConfig offset c))

theorem link_row (pre p suffix : Program) (q : Nat) (rows : Row × Row)
    (h : p[q]? = some rows) :
    (link pre p suffix)[pre.length+q]? = some (shiftPair pre.length rows) := by
  have hq : q < p.length := (List.getElem?_eq_some_iff.mp h).1
  have he : p[q] = rows := (List.getElem?_eq_some_iff.mp h).2
  simp [link,List.getElem?_append_right,List.getElem?_append_left,hq,he]

theorem execute_shift (offset : Nat) (row : Row) (tape : Tape) :
    executeRow (shiftRow offset row) tape = shiftStatus offset (executeRow row tape) := by
  rcases row with ⟨w,dir,next,tag⟩
  cases tag with
  | zero => rfl
  | succ tag => cases tag with
    | zero => rfl
    | succ tag => cases tag with
      | zero => rfl
      | succ tag => rfl

/-- Any in-range source step has an identical-time relocated step, including
invalid-result behavior and both Boolean output tags. -/
theorem step_shift (pre p suffix : Program) (c : Config) (hc : c.1 < p.length) :
    step (link pre p suffix) (shiftConfig pre.length c) =
      shiftStatus pre.length (step p c) := by
  have hp : p[c.1]? = some p[c.1] := List.getElem?_eq_getElem hc
  have hl := link_row pre p suffix c.1 p[c.1] hp
  cases hb : c.2.2.1 with
  | false =>
    have hr : rowAt p c = some p[c.1].1 := by simp [rowAt,hp,hb]
    have hs : rowAt (link pre p suffix) (shiftConfig pre.length c) =
        some (shiftRow pre.length p[c.1].1) := by simp [rowAt,shiftConfig,hl,hb,shiftPair]
    rw [step_eq_executeRow p c _ hr,step_eq_executeRow (link pre p suffix) _ _ hs]
    exact execute_shift _ _ _
  | true =>
    have hr : rowAt p c = some p[c.1].2 := by simp [rowAt,hp,hb]
    have hs : rowAt (link pre p suffix) (shiftConfig pre.length c) =
        some (shiftRow pre.length p[c.1].2) := by simp [rowAt,shiftConfig,hl,hb,shiftPair]
    rw [step_eq_executeRow p c _ hr,step_eq_executeRow (link pre p suffix) _ _ hs]
    exact execute_shift _ _ _

/-- A valid continuing row has an in-range destination. -/
theorem execute_valid_next (m : Nat) (row : Row) (tape : Tape) (d : Config)
    (hv : validRow m row = true) (h : executeRow row tape = some (.inr d)) : d.1 < m := by
  rcases row with ⟨w,dir,next,tag⟩
  cases tag with
  | zero =>
    simp only [executeRow,Option.some.injEq,Sum.inr.injEq] at h
    have hnext : next < m := by simpa [validRow] using hv
    simpa [← h] using hnext
  | succ tag => cases tag with
    | zero => simp [executeRow] at h
    | succ tag => cases tag with
      | zero => simp [executeRow] at h
      | succ tag => simp [executeRow] at h

/-- A continuing step of a valid table always points to one of its rows. -/
theorem valid_step_next (p : Program) (hvalid : valid p = true) (c d : Config)
    (h : step p c = some (.inr d)) : d.1 < p.length := by
  cases hp : p[c.1]? with
  | none => simp [step,hp] at h
  | some rows =>
    obtain ⟨hq,he⟩ := List.getElem?_eq_some_iff.mp hp
    have hmem : rows ∈ p := by rw [←he]; exact List.getElem_mem hq
    have hall : ∀ r ∈ p, validRow p.length r.1 = true ∧ validRow p.length r.2 = true := by
      have hv := hvalid
      simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
      intro r hr
      have hh := hv.2 r hr
      simpa only [Bool.and_eq_true] using hh
    have hv := hall rows hmem
    cases hb : c.2.2.1 with
    | false =>
      have hr := step_eq_executeRow p c rows.1 (by simp [rowAt,hp,hb])
      rw [hr] at h
      exact execute_valid_next p.length rows.1 c.2 d hv.1 h
    | true =>
      have hr := step_eq_executeRow p c rows.2 (by simp [rowAt,hp,hb])
      rw [hr] at h
      exact execute_valid_next p.length rows.2 c.2 d hv.2 h

def InRange (p : Program) : Status → Prop
  | some (.inr c) => c.1 < p.length
  | _ => True

theorem advance_in_range (p : Program) (hvalid : valid p = true) (s : Status)
    (hs : InRange p s) : InRange p (advance p s) := by
  cases s with
  | none => trivial
  | some v =>
    cases v with
    | inl b => trivial
    | inr c =>
      change InRange p (step p c)
      cases hstep : step p c with
      | none => trivial
      | some result =>
        cases result with
        | inl b => trivial
        | inr d => exact valid_step_next p hvalid c d hstep

theorem run_in_range (p : Program) (hvalid : valid p = true) (c : Config)
    (hc : c.1 < p.length) (n : Nat) : InRange p (run p c n) := by
  induction n with
  | zero => exact hc
  | succ n ih => exact advance_in_range p hvalid _ ih

theorem advance_shift (pre p suffix : Program) (s : Status) (hs : InRange p s) :
    advance (link pre p suffix) (shiftStatus pre.length s) =
      shiftStatus pre.length (advance p s) := by
  cases s with
  | none => rfl
  | some v => cases v with
    | inl b => rfl
    | inr c => exact step_shift pre p suffix c hs

/-- Every bounded run of a valid table is reproduced behind an arbitrary
prefix and suffix, in exactly the same number of transitions. -/
theorem run_shift (pre p suffix : Program) (hvalid : valid p = true)
    (c : Config) (hc : c.1 < p.length) (n : Nat) :
    run (link pre p suffix) (shiftConfig pre.length c) n =
      shiftStatus pre.length (run p c n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run_succ,ih]
    exact advance_shift pre p suffix _ (run_in_range p hvalid c hc n)

theorem valid_nonempty (p : Program) (hvalid : valid p = true) : 0 < p.length := by
  cases p with
  | nil => simp [valid] at hvalid
  | cons row rows => simp

/-- Once a wrapper reaches the relocated initial configuration of `payload`,
it preserves the candidate's result or timeout after exactly `n` more steps. -/
theorem bounded_after_setup (pre p suffix : Program) (hvalid : valid p = true)
    (input payload : List Bool) (setup n : Nat)
    (hentry : run (link pre p suffix) (initial input) setup =
      some (.inr (shiftConfig pre.length (initial payload)))) :
    bounded (link pre p suffix) input (setup+n) = bounded p payload n := by
  unfold bounded
  rw [run_continue _ _ _ _ _ hentry,run_shift pre p suffix hvalid _ (by simpa [initial] using valid_nonempty p hvalid)]
  cases h : run p (initial payload) n with
  | none => rfl
  | some v => cases v <;> rfl

/-- The existing total repair turns any linked table into a valid table while
retaining the exact bounded result, including timeout and failure. -/
theorem valid_link_after_setup (pre p suffix : Program) (hvalid : valid p = true)
    (input payload : List Bool) (setup n : Nat)
    (hentry : run (link pre p suffix) (initial input) setup =
      some (.inr (shiftConfig pre.length (initial payload)))) :
    valid (Shared.Codes.FiniteProgramRepair.repair (link pre p suffix)) = true ∧
      bounded (Shared.Codes.FiniteProgramRepair.repair (link pre p suffix)) input (setup+n) = bounded p payload n := by
  constructor
  · exact Shared.Codes.FiniteProgramRepair.repair_valid _
  · rw [Shared.Codes.FiniteProgramRepair.bounded_repair]
    exact bounded_after_setup pre p suffix hvalid input payload setup n hentry

theorem result_shift (offset : Nat) (s : Status) :
    FiniteProgramTapeEquiv.result (shiftStatus offset s) = FiniteProgramTapeEquiv.result s := by
  cases s with
  | none => rfl
  | some v => cases v <;> rfl

/-- A wrapper may leave redundant blank cells on either side of the head.
The entry condition and its setup time remain explicit obligations. -/
theorem bounded_after_setup_tape (pre p suffix : Program) (hvalid : valid p = true)
    (input payload : List Bool) (c : Config) (setup n : Nat)
    (hcstate : c.1 = 0)
    (htape : FiniteProgramTapeEquiv.TapeRel c.2 (initial payload).2)
    (hentry : run (link pre p suffix) (initial input) setup =
      some (.inr (shiftConfig pre.length c))) :
    bounded (link pre p suffix) input (setup+n) = bounded p payload n := by
  have hc : c.1 < p.length := by rw [hcstate]; exact valid_nonempty p hvalid
  unfold bounded
  rw [run_continue _ _ _ _ _ hentry,run_shift pre p suffix hvalid c hc]
  change FiniteProgramTapeEquiv.result (shiftStatus pre.length (run p c n)) =
    FiniteProgramTapeEquiv.result (run p (initial payload) n)
  rw [result_shift]
  exact FiniteProgramTapeEquiv.run_result_congr p c (initial payload)
    (by simpa [initial] using hcstate) htape n

theorem valid_link_after_setup_tape (pre p suffix : Program) (hvalid : valid p = true)
    (input payload : List Bool) (c : Config) (setup n : Nat)
    (hcstate : c.1 = 0)
    (htape : FiniteProgramTapeEquiv.TapeRel c.2 (initial payload).2)
    (hentry : run (link pre p suffix) (initial input) setup =
      some (.inr (shiftConfig pre.length c))) :
    valid (Shared.Codes.FiniteProgramRepair.repair (link pre p suffix)) = true ∧
      bounded (Shared.Codes.FiniteProgramRepair.repair (link pre p suffix)) input (setup+n) =
        bounded p payload n := by
  constructor
  · exact Shared.Codes.FiniteProgramRepair.repair_valid _
  · rw [Shared.Codes.FiniteProgramRepair.bounded_repair]
    exact bounded_after_setup_tape pre p suffix hvalid input payload c setup n hcstate htape hentry

end Shared.Codes.FiniteProgramLink
