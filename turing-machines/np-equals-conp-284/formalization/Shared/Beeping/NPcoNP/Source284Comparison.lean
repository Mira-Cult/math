import Shared.Beeping.NPcoNP.Source284ParserComputable
import Shared.Beeping.NPcoNP.Source284RelativeComputable

/-! The exact mathematical comparison performed by the selected 284-state
source, before any source-program or finite-table refinement. Both bounded
acceptance phases are existential; equality refutes the current candidate.

Source: `problems/np-conp-formulations/selector/continuation/compact/
phase_swap/source.py`, Mira-Cult/math-wip revision
`7b90875183aa928fb19a4a9bf333b8ced2194ded`, SHA-256
`4f1f6f317eb196b8d09a67439893622a759c43ef4e02e30adae4e04b0eb39515`.
All natural descriptions are meaningful and timeout is rejection. The
candidate receives the full input integer, including the ignored suffix.
No complexity-class characterization or compiler refinement is asserted. -/

namespace Shared.Beeping.NPcoNP.Source284Comparison

open Shared.Beeping.NPcoNP.Source284Relative

/-- Candidate description `j` is also the fixed exponent. -/
def clock (j i : Nat) : Nat := (Source284Parser.length i + 1) ^ j

/-- The source's reference phase tries certificates below `D(i)`. -/
def reference (i : Nat) : Bool :=
  acceptBound (Source284Parser.description i) 0 (Source284Parser.length i) (Source284Parser.description i)

/-- The candidate phase starts on all bits of `i` and tries `2^clock` certificates. -/
def candidate (j i : Nat) : Bool :=
  acceptBound j i (clock j i) (2 ^ clock j i)

/-- The source proceeds silently exactly when the two bits differ. -/
def compare (j i : Nat) : Bool := !(reference i == candidate j i)

/-- The source sets `expected` to the reference bit, then toggles it exactly
when the candidate accepts. Its final zero check rejects the candidate. -/
def sourceToggle (expected accepted : Bool) : Bool :=
  if accepted then !expected else expected

theorem compare_eq_sourceToggle (j i : Nat) :
    compare j i = sourceToggle (reference i) (candidate j i) := by
  cases h1 : reference i <;> cases h2 : candidate j i <;> simp [compare, sourceToggle, h1, h2]

@[simp] theorem clock_zero_exponent (i : Nat) : clock 0 i = 1 := by
  simp [clock]

theorem clock_empty_prefix (j i : Nat) (h : Source284Parser.length i = 0) :
    clock j i = 1 := by simp [clock, h]

theorem compare_true_iff (j i : Nat) :
    compare j i = true ↔ reference i ≠ candidate j i := by
  cases h1 : reference i <;> cases h2 : candidate j i <;> simp [compare, h1, h2]

theorem compare_false_iff (j i : Nat) :
    compare j i = false ↔ reference i = candidate j i := by
  cases h1 : reference i <;> cases h2 : candidate j i <;> simp [compare, h1, h2]

theorem clock_primrec : Primrec₂ clock := by
  have hp : Primrec₂ ((· ^ ·) : Nat → Nat → Nat) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  exact (hp.comp (Primrec.succ.comp (Source284Parser.length_primrec.comp Primrec.snd)) Primrec.fst).to₂

theorem reference_primrec : Primrec reference := by
  have hd : Primrec Source284Parser.description := Source284Parser.description_primrec
  have hn : Primrec Source284Parser.length := Source284Parser.length_primrec
  exact boundedAcceptance_primrec.comp
    (Primrec.pair (Primrec.pair (Primrec.pair hd (Primrec.const 0)) hn) hd)

theorem candidate_primrec : Primrec₂ candidate := by
  have hc : Primrec (fun p : Nat × Nat => clock p.1 p.2) := clock_primrec
  have hp : Primrec₂ ((· ^ ·) : Nat → Nat → Nat) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hb : Primrec (fun p : Nat × Nat => 2 ^ clock p.1 p.2) :=
    hp.comp (Primrec.const 2) hc
  exact (boundedAcceptance_primrec.comp
    (Primrec.pair (Primrec.pair (Primrec.pair Primrec.fst Primrec.snd) hc) hb)).to₂

theorem compare_primrec : Primrec₂ compare := by
  exact (Primrec.not.comp
    (Primrec.beq.comp (reference_primrec.comp Primrec.snd) candidate_primrec)).to₂

theorem compare_computable : Computable₂ compare := compare_primrec.to_comp

/-- Candidate zero accepts every input in one transition. -/
theorem candidate_zero (i : Nat) : candidate 0 i = true := by
  simp only [candidate, clock, Nat.pow_zero]
  apply (acceptBound_iff 0 i 1 (2 ^ 1)).2
  exact ⟨0, by decide, accepts_zero_description_one i 0⟩

theorem parse_zero : Source284Parser.parse 0 = (0,1) := Source284Parser.run_even 0 0 1 (by decide)

theorem parse_one : Source284Parser.parse 1 = (1,2) := by
  change Source284Parser.run 1 0 1 = _
  calc
    Source284Parser.run 1 0 1 = Source284Parser.run 0 1 2 := Source284Parser.run_odd 1 0 1 (by decide)
    _ = (1,2) := Source284Parser.run_even 0 1 2 (by decide)

example : compare 0 0 = true := by
  have hr : reference 0 = false := by
    simp [reference, Source284Parser.length, Source284Parser.description, parse_zero]
  simp [compare, hr, candidate_zero]

example : compare 0 1 = false := by
  have hr : reference 1 = true := by
    simp only [reference, Source284Parser.length, Source284Parser.description, parse_one]
    apply (acceptBound_iff 2 0 1 2).2
    refine ⟨0, by decide, ?_⟩
    have hr : record 2 0 = 0 := by
      simp [record, dropRecords, readRecord_even 2 (by decide)]
    simp [accepts, run, initial, step, hr]
  simp [compare, hr, candidate_zero]

end Shared.Beeping.NPcoNP.Source284Comparison
