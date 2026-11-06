import Shared.Codes.FiniteProgramFirstEntry

namespace Shared.Codes.FiniteProgramFirstEntry
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (run_in_range InRange)

/-- Simultaneously replace any collection of terminal rows. A source run
ending in a live configuration cannot have previously entered any such row,
so every transition before the final live configuration is preserved. The
terminal result may differ between rows. -/
theorem first_entry_many (p q : Program) (c last : Config) (n : Nat) (stops : Set Nat)
    (hvalid : valid p = true) (hc : c.1 < p.length)
    (hstop : ∀ s ∈ stops, ∃ result, ∀ t, step p (s,t) = some (.inl result))
    (hsame : ∀ d, d.1 < p.length → d.1 ∉ stops → step p d = step q d)
    (hfinal : run p c n = some (.inr last)) : run q c n = some (.inr last) := by
  have hnot : ∀ i < n, ∀ d, run p c i = some (.inr d) → d.1 ∉ stops := by
    intro i hi d hr hmem
    obtain ⟨result,hs⟩ := hstop d.1 hmem
    exact not_visited_before p c last n d.1 result hs hfinal i hi d hr rfl
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
