import Shared.Codes.FiniteProgramLink

/-! Change a finite table at a terminal row while preserving a run that ends
on its first entry to that row. No progress or termination beyond the entry
is assumed. -/
namespace Shared.Codes.FiniteProgramFirstEntry
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (run_in_range InRange)

/-- A final live configuration at a result row cannot have visited that row
at any earlier time: the next step would have produced a stable result. -/
theorem not_visited_before (p : Program) (c last : Config) (n stop : Nat) (result : Bool)
    (hstop : ∀ t, step p (stop,t) = some (.inl result))
    (hfinal : run p c n = some (.inr last)) :
    ∀ i < n, ∀ d, run p c i = some (.inr d) → d.1 ≠ stop := by
  intro i hi d hr he
  have hs : step p d = some (.inl result) := by
    cases d with
    | mk q t => simp only at he; subst q; exact hstop t
  have hnext : run p c (i+1) = some (.inl result) := by
    rw [run_succ,hr]
    exact hs
  have hend := run_result_stable p c (show i+1 ≤ n by omega) hnext
  rw [hend] at hfinal
  cases hfinal

/-- For a valid source table, preserving every in-range row except its
terminal row preserves any run that stops live on that row. -/
theorem first_entry (p q : Program) (c last : Config) (n stop : Nat) (result : Bool)
    (hvalid : valid p = true) (hc : c.1 < p.length)
    (hstop : ∀ t, step p (stop,t) = some (.inl result))
    (hsame : ∀ d, d.1 < p.length → d.1 ≠ stop → step p d = step q d)
    (hfinal : run p c n = some (.inr last)) : run q c n = some (.inr last) := by
  have hnot := not_visited_before p c last n stop result hstop hfinal
  have heq : ∀ i ≤ n, run p c i = run q c i := by
    intro i hi
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [run_succ,run_succ,← ih (by omega)]
      cases hr : run p c i with
      | none => rfl
      | some v => cases v with
        | inl b => rfl
        | inr d =>
          change step p d = step q d
          have hin := run_in_range p hvalid c hc i
          rw [hr] at hin
          exact hsame d hin (hnot i (by omega) d hr)
  rw [← heq n (by omega)]
  exact hfinal

end Shared.Codes.FiniteProgramFirstEntry
