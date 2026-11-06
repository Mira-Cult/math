import Shared.Beeping.NPcoNP.Source284SATPartialSoundness
import Shared.Beeping.NPcoNP.Source284Truncation

/-! A verifier can tolerate arbitrary high input bits provided its finite
execution cannot reach them. This SAT-specific interface is a component of
the proposed fixed-window certificate validator. It does not implement that
validator, a rewind, a reduction, or the physical 284-state machine. -/

namespace Shared.Beeping.NPcoNP.Source284SATWindowSoundness

open Shared.Codes.FinitePrograms
open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284Relative
open Shared.Beeping.NPcoNP.Source284BitWindow
open Shared.Beeping.NPcoNP.Source284SATPartialSoundness

/-- A clock-bounded source evaluator observes only the corresponding input
window. High bits are not required to be zero or physically erased. -/
theorem accepts_input_window (description input replacement certificate clock : Nat)
    (h : Agree clock input replacement) :
    accepts description input certificate clock =
      accepts description replacement certificate clock := by
  have hw : Window clock (initial input certificate) (initial replacement certificate) :=
    ⟨rfl, agree_refl _ _, h⟩
  have hr := run_window description clock 0 _ _ (by simpa using hw)
  simp only [accepts, hr.1]

/-- For one fixed valid SAT verifier, arbitrary input bits outside the first
`window` cells cannot counterfeit SAT in any execution of at most `window`
steps. This does not construct or validate the claimed low window. -/
theorem sat_fixed_verifier_window_sound :
    ∃ (program : Program) (clock : Polynomial Nat), valid program = true ∧
      (∀ (x w : List Bool) (fuel window input : Nat), fuel ≤ window →
        input % 2^window = value (BitstringEncoding.bitEncode (x,w)) →
        Source284Relative.accepts
          (value (Shared.Beeping.NPcoNP.Source284CompileBitsTM2.compileBits program))
          input 0 fuel = true →
        Shared.ComplexityBridge.CNF.sat x = true) ∧
      (∀ x : List Bool, Shared.ComplexityBridge.CNF.sat x = true →
        ∃ w : List Bool, w.length ≤ x.length ∧
          Source284Relative.accepts
            (value (Shared.Beeping.NPcoNP.Source284CompileBitsTM2.compileBits program))
            (value (BitstringEncoding.bitEncode (x,w))) 0
            (Shared.ComplexityBridge.BoundedHardness.commonFuel Polynomial.X clock x) = true) := by
  obtain ⟨program, clock, hv, hsound, hcomplete⟩ := sat_verifier_partial_sound
  refine ⟨program, clock, hv, ?_, ?_⟩
  · intro x w fuel window input hfuel hlow haccept
    have hinput : Agree window input (value (BitstringEncoding.bitEncode (x,w))) := by
      rw [← hlow]
      exact agree_truncate _ _
    have heq := accepts_input_window
      (value (Shared.Beeping.NPcoNP.Source284CompileBitsTM2.compileBits program))
      input (value (BitstringEncoding.bitEncode (x,w))) 0 fuel
      (agree_mono hfuel hinput)
    have hfinite := (Shared.Beeping.NPcoNP.Source284CompileBitsTM2.bounded_acceptance
      program hv (BitstringEncoding.bitEncode (x,w)) fuel).1 (heq ▸ haccept)
    have htable := (Shared.Beeping.NPcoNP.Source284FiniteRelativeRun.bounded_acceptance
      program (BitstringEncoding.bitEncode (x,w)) fuel hv).2 hfinite
    exact hsound x w fuel htable
  · intro x hx
    obtain ⟨w, hw, htable⟩ := hcomplete x hx
    refine ⟨w, hw, ?_⟩
    apply (Shared.Beeping.NPcoNP.Source284CompileBitsTM2.bounded_acceptance
      program hv (BitstringEncoding.bitEncode (x,w)) _).2
    exact (Shared.Beeping.NPcoNP.Source284FiniteRelativeRun.bounded_acceptance
      program (BitstringEncoding.bitEncode (x,w)) _ hv).1 htable

end Shared.Beeping.NPcoNP.Source284SATWindowSoundness
