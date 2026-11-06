import Shared.Beeping.NPcoNP.Source284SATRelativeRun

/-! SAT-specific soundness for witnesses of arbitrary length and verifier
execution stopped at any clock. The canonical SAT checker is sound even for
oversized witnesses. The arbitrary-clock claim uses determinism and the
separately established total correctness of the finite verifier; it does not
implement certificate decoding, a witness loader, or candidate coverage. -/

namespace Shared.Beeping.NPcoNP.Source284SATPartialSoundness

open Shared.Codes.FinitePrograms
open Shared.Beeping.NPcoNP.Source284ListTables
open Shared.Beeping.NPcoNP.Source284FiniteRelativeRows
open Shared.Beeping.NPcoNP.Source284FiniteRelativeRun
open Shared.Beeping.NPcoNP.Source284SATVerifier
open Shared.ComplexityBridge.BoundedHardness
open Shared.Codes.BitNumeralCompare (value)

/-- Any two Boolean results returned by one deterministic finite program on
the same input, even at different fuel bounds, are equal. -/
theorem bounded_unique (p : Program) (input : List Bool) (m n : Nat)
    (a b : Bool) (ha : bounded p input m = some a)
    (hb : bounded p input n = some b) : a = b := by
  obtain ⟨ta, _, hra⟩ := (bounded_iff_result p input m a).1 ha
  obtain ⟨tb, _, hrb⟩ := (bounded_iff_result p input n b).1 hb
  have ha' := run_result_stable p (initial input) (le_max_left ta tb) hra
  have hb' := run_result_stable p (initial input) (le_max_right ta tb) hrb
  rw [ha'] at hb'
  cases hb'
  rfl

/-- Any accepting occurrence-assignment witness implies SAT, regardless of
its length. This uses the all-bitstrings parser, including malformed inputs. -/
theorem verify_sound_unbounded (x w : List Bool)
    (h : Shared.ComplexityBridge.CNFWitness.verify (x,w) = true) :
    Shared.ComplexityBridge.CNF.sat x = true := by
  apply (Shared.ComplexityBridge.CNF.sat_correct x).mpr
  cases hp : Shared.ComplexityBridge.CNF.parse x with
  | none => simp [Shared.ComplexityBridge.CNFWitness.verify, hp] at h
  | some formula =>
    refine ⟨formula, rfl, ?_⟩
    refine ⟨Shared.ComplexityBridge.CNF.assignment
      (Shared.ComplexityBridge.CNF.variableOccurrences formula) w, ?_⟩
    simpa [Shared.ComplexityBridge.CNFWitness.verify, hp] using h

/-- One valid finite relative verifier has arbitrary-clock soundness for
every list witness, while bounded witnesses retain the original common-clock
completeness theorem. This is source-table semantics, not the separate
certificate-to-pair loader or the physical 284-state machine. -/
theorem sat_verifier_partial_sound :
    ∃ (program : Program) (clock : Polynomial Nat), valid program = true ∧
      (∀ (x w : List Bool) (fuel : Nat),
        (Source284TableRun.run (table (rows program))
          ⟨0, value (BitstringEncoding.bitEncode (x,w)), some 0⟩ fuel).state.isNone = true →
            Shared.ComplexityBridge.CNF.sat x = true) ∧
      (∀ x : List Bool, Shared.ComplexityBridge.CNF.sat x = true →
        ∃ w : List Bool, w.length ≤ x.length ∧
          (Source284TableRun.run (table (rows program))
            ⟨0, value (BitstringEncoding.bitEncode (x,w)), some 0⟩
            (commonFuel Polynomial.X clock x)).state.isNone = true) := by
  obtain ⟨p, clock, hv, hp⟩ :=
    valid_pair_verifier Shared.ComplexityBridge.CNFWitness.verify
      Shared.ComplexityBridge.TM2PreparedVerify.verify_isPolyTime
  refine ⟨p, clock, hv, ?_, ?_⟩
  · intro x w fuel h
    have ha := (bounded_acceptance p (BitstringEncoding.bitEncode (x,w)) fuel hv).1 h
    have hb := hp x w
    have he := bounded_unique p (BitstringEncoding.bitEncode (x,w)) fuel
      (clock.eval (BitstringEncoding.bitEncode (x,w)).length) true
      (Shared.ComplexityBridge.CNFWitness.verify (x,w)) ha hb
    exact verify_sound_unbounded x w he.symm
  · intro x hx
    obtain ⟨w, hw, hverify⟩ :=
      (Shared.ComplexityBridge.CNFWitness.sat_iff_bounded_verifier x).mp hx
    refine ⟨w, hw, ?_⟩
    apply (bounded_acceptance p (BitstringEncoding.bitEncode (x,w)) _ hv).2
    rw [commonFuel_correct Shared.ComplexityBridge.CNFWitness.verify p
      Polynomial.X clock hp x w (by simpa using hw), hverify]

end Shared.Beeping.NPcoNP.Source284SATPartialSoundness
