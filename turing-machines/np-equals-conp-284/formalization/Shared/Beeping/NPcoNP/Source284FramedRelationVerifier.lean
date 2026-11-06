import Shared.Beeping.NPcoNP.Source284CanonicalFrameTM2
import Shared.Beeping.NPcoNP.Source284CanonicalTaggedVerifier
import Shared.Beeping.NPcoNP.Source284PackedGuardIsolation

/-! A single finite source verifier for a canonical polynomial-time Boolean
relation on a prepared framed witness. Its polynomial runtime depends on the
original witness cutoff; constructing the prepared window remains open. -/
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace Shared.Beeping.NPcoNP.Source284FramedRelationVerifier

open ComplexityTheory Shared.ComplexityBridge
open Shared.Codes.FinitePrograms
open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284RawParse (payload)
open Shared.Beeping.NPcoNP.Source284Parser (frameBits)
open Shared.Beeping.NPcoNP.Source284Relative (Window)

/-- The parser is total, including malformed frames and virtual zeros. -/
def relation (R : List Bool × List Bool → Bool) (p : List Bool × List Bool) : Bool :=
  R (p.1,payload p.2)

theorem relation_isPolyTime (R : List Bool × List Bool → Bool) (hR : IsPolyTime R) :
    IsPolyTime (relation R) := by
  let first : List Bool × List Bool → List Bool := fun p => p.1
  let second : List Bool × List Bool → List Bool := fun p => p.2
  have hf : IsPolyTime first := TM2PairFirst.first_isPolyTime
  have hs : IsPolyTime second := TM2GuardAllStep.second_isPolyTime
  have hp : IsPolyTime (fun p => payload (second p)) :=
    TM2Compose.isPolyTime_comp second payload hs Source284RawParseTM2.payload_isPolyTime
  exact TM2Compose.isPolyTime_comp (fun p => (first p,payload (second p))) R
    (TM2GuardAllStep.pair_isPolyTime first (fun p => payload (second p)) hf hp) hR

theorem relation_frame (R : List Bool × List Bool → Bool) (x w : List Bool) :
    relation R (x,frameBits w [true]) = R (x,w) := by
  simp [relation,Source284WitnessWindow.payload_frame]

/-- The verifier's complete input counts both x and the framed witness in
the Google pair encoding, including the frame's delimiter and sentinel. -/
theorem packed_frame_length (x w : List Bool) :
    (BitstringEncoding.bitEncode (x,frameBits w [true])).length =
      6*x.length+6*w.length+7 := by
  rw [Shared.ComplexityBridge.bitstring_pair_encoded_length,Source284WitnessWindow.frame_length]
  omega

/-- One finite source program works for every pair relation instance and
all witnesses within the original cutoff. Its clock is a polynomial in the
full input and cutoff lengths. This verifier does not reject overlong witnesses;
a preceding cutoff guard must enforce that condition. The caller must also
establish the stated concrete prepared-window condition. -/
theorem source_verifier (R : List Bool × List Bool → Bool) (hR : IsPolyTime R) :
    ∃ (program : Program) (clock : Polynomial Nat), valid program = true ∧
      ∀ (x w : List Bool) (limit : Nat), w.length ≤ limit →
      ∀ (c : Source284Relative.Config) (extra : Nat),
        let packed := BitstringEncoding.bitEncode (x,frameBits w [true])
        let t := clock.eval (6*x.length+6*limit+7)
        Window t c (Source284Relative.initial (value packed) 0) →
        ((Source284Relative.run (Source284CompileRecords.compile program) c (t+extra)).state == 0) = R (x,w) := by
  obtain ⟨raw,clock,hcorrect⟩ := FiniteVerifierCompiler.canonical_finite_verifier_compiler
    (relation R) (relation_isPolyTime R hR)
  let program := Shared.Codes.FiniteProgramRepair.repair raw
  refine ⟨program,clock,Shared.Codes.FiniteProgramRepair.repair_valid raw,?_⟩
  intro x w limit hw c extra
  dsimp only
  intro hwindow
  let packed := BitstringEncoding.bitEncode (x,frameBits w [true])
  let t := clock.eval (6*x.length+6*limit+7)
  have hlen : packed.length ≤ 6*x.length+6*limit+7 := by
    dsimp only [packed]
    rw [packed_frame_length]
    omega
  have hclock : clock.eval packed.length ≤ t := TM2Compose.polynomial_eval_mono clock hlen
  have hsmall := hcorrect x (frameBits w [true])
  rw [relation_frame] at hsmall
  have hbounded : bounded program packed t = some (R (x,w)) := by
    dsimp only [program]
    rw [Shared.Codes.FiniteProgramRepair.bounded_repair]
    exact BoundedHardness.bounded_mono raw packed (clock.eval packed.length) t (R (x,w)) hclock hsmall
  exact Source284PackedGuardIsolation.compiled_window_stable program packed t (R (x,w))
    (Shared.Codes.FiniteProgramRepair.repair_valid raw) hbounded c hwindow extra

end Shared.Beeping.NPcoNP.Source284FramedRelationVerifier
