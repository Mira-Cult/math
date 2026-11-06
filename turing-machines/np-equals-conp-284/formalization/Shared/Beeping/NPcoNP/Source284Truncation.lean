import Shared.Beeping.NPcoNP.Source284Relative
import Shared.Beeping.NPcoNP.Source284BitWindow
import Shared.Beeping.NPcoNP.Source284Oversupply

/-! Finite influence of the certificate half-tape for the 284 source's
bounded relative-direction evaluator. No claim is made that full tapes agree
after truncation: only the observed finite windows and accepting state do. -/
namespace Shared.Beeping.NPcoNP.Source284Relative
open Shared.Beeping.NPcoNP.Source284BitWindow

/-- Equal control and equal low `k` cells on both oriented tape halves. -/
def Window (k : Nat) (a b : Config) : Prop :=
  a.state = b.state ∧ Agree k a.left b.left ∧ Agree k a.right b.right

/-- One transition consumes at most one observable cell from either half;
turning may swap the halves and writing prepends one equal bit. -/
theorem step_window (description k : Nat) (a b : Config)
    (h : Window (k+1) a b) : Window k (step description a) (step description b) := by
  rcases a with ⟨al, ar, sa⟩
  rcases b with ⟨bl, br, sb⟩
  rcases h with ⟨hs, hl, hr⟩
  change sa = sb at hs
  subst sb
  have hread : ar % 2 = br % 2 := agree_head hr
  by_cases hz : sa = 0
  · simpa [step, hz, Window] using
      (show sa = sa ∧ Agree k al bl ∧ Agree k ar br from
        ⟨rfl, agree_weaken hl, agree_weaken hr⟩)
  · by_cases ht : (record description (sa - 1 + br % 2) / 2) % 2 = 1
    · simp only [step, hz, ↓reduceIte, hread, ht, Window]
      exact ⟨trivial, agree_push (agree_tail hr) _, agree_weaken hl⟩
    · simp only [step, hz, ↓reduceIte, hread, ht, Window]
      exact ⟨trivial, agree_push (agree_weaken hl) _, agree_tail hr⟩

/-- After `clock` steps, at most that many cells of each starting half can
have influenced the result. The remaining low `k` cells still agree. -/
theorem run_window (description clock k : Nat) (a b : Config)
    (h : Window (k+clock) a b) :
    Window k (run description a clock) (run description b clock) := by
  induction clock generalizing k with
  | zero => simpa using h
  | succ clock ih =>
    have h' : Window ((k+1)+clock) a b := by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    have hm := ih (k+1) h'
    simpa only [run_succ] using step_window description k _ _ hm

/-- A `clock`-step attempt observes at most the low `clock` certificate
bits. Higher bits may remain on the tape and are not asserted equal. -/
theorem accepts_truncate (description input certificate clock : Nat) :
    accepts description input certificate clock =
      accepts description input (certificate % 2^clock) clock := by
  have h : Window clock (initial input certificate)
      (initial input (certificate % 2^clock)) := by
    exact ⟨rfl, agree_truncate _ _, agree_refl _ _⟩
  have hr := run_window description clock 0 _ _ (by simpa using h)
  simp only [accepts, hr.1]

/-- Oversupplying certificates cannot change bounded acceptance: every
attempt has an equivalent representative below `2^clock`. -/
theorem acceptBound_oversupply (description input clock bound : Nat)
    (hb : 2^clock ≤ bound) :
    acceptBound description input clock bound =
      acceptBound description input clock (2^clock) := by
  exact Shared.Beeping.NPcoNP.Source284Parser.range_any_oversupply clock bound
    (fun certificate => accepts description input certificate clock) hb
    (fun certificate => accepts_truncate description input certificate clock)

end Shared.Beeping.NPcoNP.Source284Relative
