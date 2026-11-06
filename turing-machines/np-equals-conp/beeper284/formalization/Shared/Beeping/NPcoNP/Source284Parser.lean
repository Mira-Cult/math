import Mathlib.Tactic

/-! The marker/payload normalizer used by the NP=coNP 284-state source.

Provenance: `problems/np-conp-formulations/selector/continuation/compact/phase_swap/source.py`,
in Mira-Cult/math-wip commit
`7b90875183aa928fb19a4a9bf333b8ced2194ded`, source SHA-256
`4f1f6f317eb196b8d09a67439893622a759c43ef4e02e30adae4e04b0eb39515`.
The source starts with `(scan,n,e)=(i,0,1)`; while the marker bit is one,
it consumes that bit, appends the next bit to `e`, then consumes that bit.
The first zero marker and all higher bits are ignored by the returned pair.
This module does not identify any compiled machine or assert a complexity
class equality. -/

namespace Shared.Beeping.NPcoNP.Source284Parser

/-- The source's finite parser with explicit length and description
accumulators. Natural-number division supplies virtual zero high bits. -/
def run (scan n e : Nat) : Nat × Nat :=
  if scan % 2 = 1 then
    run (scan / 4) (n + 1) (2 * e + (scan / 2) % 2)
  else
    (n, e)
termination_by scan
decreasing_by
  have hs : 0 < scan := by omega
  exact Nat.div_lt_self hs (by decide)

def parse (i : Nat) : Nat × Nat := run i 0 1
def length (i : Nat) : Nat := (parse i).1
def description (i : Nat) : Nat := (parse i).2

theorem run_odd (scan n e : Nat) (h : scan % 2 = 1) :
    run scan n e = run (scan / 4) (n + 1) (2 * e + (scan / 2) % 2) := by
  rw [run]
  simp [h]

theorem run_even (scan n e : Nat) (h : scan % 2 = 0) :
    run scan n e = (n,e) := by
  rw [run]
  simp [h]

/-- One odd-marker iteration has precisely the effect of the source's
two sequential halvings and the conditional payload increment. -/
theorem source_odd_step (scan n e : Nat) (h : scan % 2 = 1) :
    run scan n e =
      run ((scan / 2) / 2) (n + 1)
        (if (scan / 2) % 2 = 1 then 2 * e + 1 else 2 * e) := by
  rw [run_odd scan n e h]
  have hdiv : (scan / 2) / 2 = scan / 4 := by omega
  rw [hdiv]
  by_cases hbit : (scan / 2) % 2 = 1
  · simp [hbit]
  · have hz : (scan / 2) % 2 = 0 := by omega
    simp [hz]

/-- Every even input has an empty prefix, regardless of its upper bits. -/
theorem even_input (i : Nat) (h : i % 2 = 0) : parse i = (0,1) := by
  exact run_even i 0 1 h

/-- Appending either payload bit preserves the sentinel interval. -/
theorem append_bounds (n e bit : Nat) (hb : bit < 2)
    (hl : 2^n ≤ e) (hu : e < 2^(n+1)) :
    2^(n+1) ≤ 2*e+bit ∧ 2*e+bit < 2^((n+1)+1) := by
  simp only [pow_succ] at *
  constructor <;> nlinarith

/-- The source loop preserves the sentinel interval for arbitrary finite
scan values and arbitrary accumulators satisfying that interval. -/
theorem run_bounds (scan n e : Nat) (hl : 2^n ≤ e) (hu : e < 2^(n+1)) :
    2^(run scan n e).1 ≤ (run scan n e).2 ∧
      (run scan n e).2 < 2^((run scan n e).1+1) := by
  induction scan using Nat.strong_induction_on generalizing n e with
  | h scan ih =>
    by_cases h : scan % 2 = 1
    · rw [run_odd scan n e h]
      have hs : 0 < scan := by omega
      have hlt : scan / 4 < scan := Nat.div_lt_self hs (by decide)
      have hb : (scan / 2) % 2 < 2 := Nat.mod_lt _ (by decide)
      obtain ⟨hl',hu'⟩ := append_bounds n e ((scan / 2) % 2) hb hl hu
      exact ih (scan / 4) hlt (n + 1) (2 * e + (scan / 2) % 2) hl' hu'
    · have he : scan % 2 = 0 := by omega
      rw [run_even scan n e he]
      exact ⟨hl,hu⟩

/-- The resulting description is the binary payload with a leading one. -/
theorem sentinel_bounds (i : Nat) :
    2^(length i) ≤ description i ∧ description i < 2^((length i)+1) := by
  simpa [length, description, parse] using run_bounds i 0 1 (by decide) (by decide)

end Shared.Beeping.NPcoNP.Source284Parser
