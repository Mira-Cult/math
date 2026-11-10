import PASoundness.M236Game
import PASoundness.CompactSemantics

/-!
A separate metatheoretic finite-table construction, used only after the
structural source equivalence. It does not evaluate quantified truth in the
producer and it does not establish any connection to the physical machine.
-/
namespace PASoundness.M236Acceptance

open PASoundness.M236Game PASoundness.CompactSemantics PASoundness.CompactMatrix

/-- In Lean's metatheory, every finite set of truth values has a natural bit
code. The finite list depends classically on truth and is not producer code. -/
theorem finite_tables : FiniteTableFamily := by
  classical
  intro f A
  let xs := (List.range (A + 1)).filter (fun y => decide (Truth f [y]))
  refine ⟨finiteSetCode xs, ?_⟩
  intro y hy
  have hv : (finiteSetCode xs).testBit y = true ↔ Truth f [y] := by
    rw [← bit_eq_testBit, finiteSetCode_spec]
    have hlt : y < A + 1 := by omega
    simp [xs, hlt]
  cases hb : (finiteSetCode xs).testBit y with
  | false =>
    change ¬ Truth f [y]
    intro ht
    have hf := hv.mpr ht
    rw [hb] at hf
    cases hf
  | true =>
    change Truth f [y]
    exact hv.mp hb

/-- Acceptance of the abstract fair source only. No physical-machine claim
is made by applying finite comprehension here. -/
theorem selected_source_acceptance :
    M236Observer.TraceAccept (Source.source selectedValue) :=
  selected_source_accept_iff_finite_tables.mpr finite_tables

end PASoundness.M236Acceptance
