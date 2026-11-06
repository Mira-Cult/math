import Shared.Beeping.NPcoNP.Source284CompileRecords
import Shared.Beeping.NPcoNP.Source284FiniteTapeEncoding

/-! A run-level comparison of the shared finite-program evaluator with the
284 source's unary-record program. The finite program's `true` result is
acceptance, while `false` and invalid results use a nonaccepting source sink.
The source performs the terminal row's write and move; finite-program
terminal statuses discard the tape. Consequently the terminal relation below
compares only the accept/reject control outcome. No initial-tape loader,
polynomial cost, or physical beeper refinement is asserted here. -/

namespace Shared.Beeping.NPcoNP.Source284FiniteProgramRun

open Shared.Codes.FinitePrograms
open Shared.Beeping.NPcoNP.Source284Relative
open Shared.Beeping.NPcoNP.Source284CompileRecords
open Shared.Beeping.NPcoNP.Source284FiniteTapeStep

/-- A continuing row must point to a real program state. Invalid/false
terminal rows are allowed: both are represented by the reject sink. -/
def Closed (p : Program) : Prop :=
  ∀ (q : Nat) (hq : q < p.length) (read : Bool),
    let row := if read then p[q].2 else p[q].1
    row.2.2.2 = 0 → row.2.2.1 < p.length

/-- The existing finite-program validity check supplies exactly the
continuation bound required by this compiler. -/
theorem closed_of_valid (p : Program) (hv : valid p = true) : Closed p := by
  have hall : p.all (fun rows => validRow p.length rows.1 && validRow p.length rows.2) = true := by
    cases he : p.isEmpty <;> simp [valid, he] at hv ⊢
    exact hv
  intro q hq read
  have hmem : p[q] ∈ p := List.getElem_mem hq
  have hrow := (List.all_eq_true.mp hall) p[q] hmem
  have hrows : validRow p.length p[q].1 = true ∧ validRow p.length p[q].2 = true := by
    simpa only [Bool.and_eq_true] using hrow
  have hvalid : validRow p.length (if read then p[q].2 else p[q].1) = true := by
    cases read with
    | false => simpa using hrows.1
    | true => simpa using hrows.2
  dsimp only
  intro htag
  simpa [validRow, htag] using hvalid

/-- The live case relates the complete tape; terminal cases deliberately
forget the tape, since the shared evaluator reports its result before a
terminal write/move while the source enters a state after that move. -/
inductive Related (p : Program) : Status → Source284Relative.Config → Prop where
  | live (q : Nat) (t : Tape) (rev : Bool) (hq : q < p.length) :
      Related p (some (.inr (q,t))) (represented t rev (codeState q rev))
  | yes (c : Source284Relative.Config) (h : c.state = 0) :
      Related p (some (.inl true)) c
  | no (c : Source284Relative.Config) (h : c.state = rejectState p.length) :
      Related p (some (.inl false)) c
  | invalid (c : Source284Relative.Config) (h : c.state = rejectState p.length) :
      Related p none c

@[simp] theorem read_represented (t : Tape) (rev : Bool) (s : Nat) :
    (represented t rev s).right % 2 = Source284CompileRecords.bit t.2.1 := by
  rw [represented_read]
  cases t.2.1 <;> rfl

@[simp] theorem writeBit_pack (w t : Bool) (n : Nat) : writeBit (pack w t n) = w := by
  cases w <;> simp [writeBit, pack_write, Source284CompileRecords.bit]

@[simp] theorem turnBit_pack (w t : Bool) (n : Nat) : turnBit (pack w t n) = t := by
  cases t <;> simp [turnBit, pack_turn, Source284CompileRecords.bit]

/-- Source execution of one in-range finite row, including its real write
and move even when that row reports a terminal result. -/
theorem source_row_step (p : Program) (q : Nat) (tape : Tape) (rev : Bool)
    (hq : q < p.length) :
    let row := if tape.2.1 then p[q].2 else p[q].1
    let next := if row.2.2.2 = 0 then codeState row.2.2.1 (!row.2.1)
      else if row.2.2.2 = 2 then 0 else rejectState p.length
    Source284Relative.step (compile p) (represented tape rev (codeState q rev)) =
      represented (moveTape (!row.2.1) row.1 tape) (!row.2.1) next := by
  dsimp only
  have hpos : codeState q rev ≠ 0 := by have h := state_positive q rev; omega
  have hs := source_step_tape (compile p) tape rev (codeState q rev) hpos
  simp only [read_represented, compiled_record p q rev tape.2.1 hq, encodedRow,
    writeBit_pack, turnBit_pack, pack_next] at hs
  cases rev <;> cases hdir : (if tape.2.1 then p[q].2 else p[q].1).2.1 <;>
    simpa [Bool.xor, hdir] using hs

/-- The reserved sink is nonaccepting and stays in its reserved source state. -/
theorem sink_step (p : Program) (c : Source284Relative.Config)
    (hc : c.state = rejectState p.length) :
    (Source284Relative.step (compile p) c).state = rejectState p.length := by
  have hp : rejectState p.length ≠ 0 := by
    have h := state_positive p.length false
    simpa [rejectState] using (show codeState p.length false ≠ 0 by omega)
  have hb : c.right % 2 = Source284CompileRecords.bit (decide (c.right % 2 = 1)) := by
    have h := Nat.mod_lt c.right (by decide : 0 < 2)
    by_cases he : c.right % 2 = 1 <;> simp [Source284CompileRecords.bit, he] <;> omega
  simp only [Source284Relative.step, hc, hp, ↓reduceIte]
  rw [hb, show rejectState p.length = codeState p.length false from rfl,
    compiled_sink p false (decide (c.right % 2 = 1))]
  simp [pack_next, Source284CompileRecords.bit, rejectState]

/-- One finite-program iteration and one source iteration preserve the
relation. The in-range continuation condition is essential: virtual-zero
source records outside the compiled table can otherwise accept. -/
theorem advance_related (p : Program) (closed : Closed p)
    {status : Status} {c : Source284Relative.Config} (h : Related p status c) :
    Related p (advance p status) (Source284Relative.step (compile p) c) := by
  cases h with
  | live q tape rev hq =>
    let row := if tape.2.1 then p[q].2 else p[q].1
    have hclosed : row.2.2.2 = 0 → row.2.2.1 < p.length := by
      simpa only [row] using closed q hq tape.2.1
    have hget : p[q]? = some p[q] := by simp [hq]
    have hs := source_row_step p q tape rev hq
    dsimp only at hs
    change Related p (Shared.Codes.FinitePrograms.step p (q,tape))
      (Source284Relative.step (compile p) (represented tape rev (codeState q rev)))
    rw [hs]
    simp only [Shared.Codes.FinitePrograms.step, hget]
    change Related p
      (match row.2.2.2 with
       | 0 => some (.inr (row.2.2.1,moveTape (!row.2.1) row.1 tape))
       | 1 => some (.inl false)
       | 2 => some (.inl true)
       | _ => none)
      (represented (moveTape (!row.2.1) row.1 tape) (!row.2.1)
        (if row.2.2.2 = 0 then codeState row.2.2.1 (!row.2.1)
         else if row.2.2.2 = 2 then 0 else rejectState p.length))
    cases htag : row.2.2.2 with
    | zero =>
      simp only [Nat.succ_ne_zero, Nat.succ.injEq, ↓reduceIte]
      exact Related.live _ _ _ (hclosed htag)
    | succ k =>
      cases k with
      | zero =>
        simp only [Nat.succ_ne_zero, Nat.succ.injEq, ↓reduceIte]
        exact Related.no _ (represented_state _ _ _)
      | succ k =>
        cases k with
        | zero =>
          simp only [Nat.succ_ne_zero, Nat.succ.injEq, ↓reduceIte]
          exact Related.yes _ (represented_state _ _ _)
        | succ k =>
          simp only [Nat.succ_ne_zero, Nat.succ.injEq, ↓reduceIte]
          exact Related.invalid _ (represented_state _ _ _)
  | yes c hc =>
    simpa [advance, Source284Relative.step_absorbing _ _ hc] using Related.yes c hc
  | no c hc =>
    simpa [advance] using Related.no (Source284Relative.step (compile p) c) (sink_step p c hc)
  | invalid c hc =>
    simpa [advance] using Related.invalid (Source284Relative.step (compile p) c) (sink_step p c hc)

theorem run_related (p : Program) (closed : Closed p) (q : Nat) (t : Tape)
    (rev : Bool) (hq : q < p.length) (clock : Nat) :
    Related p (Shared.Codes.FinitePrograms.run p (q,t) clock)
      (Source284Relative.run (compile p) (represented t rev (codeState q rev)) clock) := by
  induction clock with
  | zero => exact Related.live q t rev hq
  | succ clock ih =>
    simp only [Shared.Codes.FinitePrograms.run_succ, Source284Relative.run_succ]
    exact advance_related p closed ih

/-- Related terminal configurations agree on acceptance; nonacceptance
includes a live timeout, explicit false, and invalid status. -/
theorem related_acceptance (p : Program) {status : Status} {c : Source284Relative.Config}
    (h : Related p status c) : c.state = 0 ↔ status = some (.inl true) := by
  cases h with
  | live q t rev hq =>
    have hp : codeState q rev ≠ 0 := Nat.ne_of_gt (state_positive q rev)
    simp [hp]
  | yes c hc => simp [hc]
  | no c hc =>
    have hp := state_positive p.length false
    simp [hc, rejectState, Nat.ne_of_gt hp]
  | invalid c hc =>
    have hp := state_positive p.length false
    simp [hc, rejectState, Nat.ne_of_gt hp]

/-- Equal-clock acceptance equivalence. The source may still perform a
terminal write and move; this result intentionally compares only acceptance. -/
theorem run_acceptance (p : Program) (closed : Closed p) (q : Nat) (t : Tape)
    (rev : Bool) (hq : q < p.length) (clock : Nat) :
    (Source284Relative.run (compile p) (represented t rev (codeState q rev)) clock).state = 0 ↔
      Shared.Codes.FinitePrograms.run p (q,t) clock = some (.inl true) :=
  related_acceptance p (run_related p closed q t rev hq clock)

theorem represented_initial (input : List Bool) :
    represented (Shared.Codes.FinitePrograms.initial input).2 false (codeState 0 false) =
      Source284Relative.initial (Source284FiniteTapeStep.value input) 0 := by
  cases input with
  | nil => rfl
  | cons b bs => cases b <;> rfl

/-- A forward-oriented finite tape represents exactly the source's two
numeric halves, including an arbitrary certificate on the negative side. -/
theorem represented_initial_tape (t : Tape) :
    represented t false (codeState 0 false) =
      Source284Relative.initial (Source284FiniteTapeStep.value (t.2.1 :: t.2.2))
        (Source284FiniteTapeStep.value t.1) := by
  rcases t with ⟨left,head,right⟩
  rfl

/-- Equal-clock acceptance for an arbitrary finite initial tape, including
an arbitrary negative half. This does not itself encode a witness as part of
the canonical finite verifier's public input. -/
theorem arbitrary_tape_acceptance (p : Program) (t : Tape) (clock : Nat)
    (hv : valid p = true) :
    accepts (compile p) (Source284FiniteTapeStep.value (t.2.1 :: t.2.2))
      (Source284FiniteTapeStep.value t.1) clock = true ↔
        Shared.Codes.FinitePrograms.run p (0,t) clock = some (.inl true) := by
  have hne : 0 < p.length := by
    by_contra h
    have hp : p = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [hp, valid] at hv
  have hr := run_acceptance p (closed_of_valid p hv) 0 t false hne clock
  rw [represented_initial_tape] at hr
  rw [accepts_iff]
  exact hr

/-- Public form of the arbitrary-tape theorem using the shared little-endian
numeral value, rather than the recovered local notation. -/
theorem arbitrary_tape_acceptance_shared (p : Program) (t : Tape) (clock : Nat)
    (hv : valid p = true) :
    accepts (compile p) (Shared.Codes.BitNumeralCompare.value (t.2.1 :: t.2.2))
      (Shared.Codes.BitNumeralCompare.value t.1) clock = true ↔
        Shared.Codes.FinitePrograms.run p (0,t) clock = some (.inl true) := by
  simpa only [value_eq_shared] using arbitrary_tape_acceptance p t clock hv

/-- A valid shared finite program and its compiled unary source program
accept the same finite initial-tape input at exactly the same clock. The
source certificate is zero; nonzero certificates and witness loading require
a separate adapter. -/
theorem bounded_acceptance (p : Program) (input : List Bool) (clock : Nat)
    (hv : valid p = true) :
    accepts (compile p) (Source284FiniteTapeStep.value input) 0 clock = true ↔
      bounded p input clock = some true := by
  have hne : 0 < p.length := by
    by_contra h
    have hp : p = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [hp, valid] at hv
  have hr := run_acceptance p (closed_of_valid p hv) 0
    (Shared.Codes.FinitePrograms.initial input).2 false hne clock
  rw [represented_initial] at hr
  have hinit : (0, (Shared.Codes.FinitePrograms.initial input).2) =
      Shared.Codes.FinitePrograms.initial input := by rfl
  rw [hinit] at hr
  rw [accepts_iff]
  refine hr.trans ?_
  unfold bounded
  cases hs : Shared.Codes.FinitePrograms.run p (Shared.Codes.FinitePrograms.initial input) clock with
  | none => simp [hs]
  | some x => cases x with
    | inl b => cases b <;> simp [hs]
    | inr c => simp [hs]

theorem bounded_acceptance_shared (p : Program) (input : List Bool) (clock : Nat)
    (hv : valid p = true) :
    accepts (compile p) (Shared.Codes.BitNumeralCompare.value input) 0 clock = true ↔
      bounded p input clock = some true := by
  simpa only [value_eq_shared] using bounded_acceptance p input clock hv

end Shared.Beeping.NPcoNP.Source284FiniteProgramRun
