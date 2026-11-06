import Shared.Beeping.NPcoNP.Source284TaggedBitDecode
import Shared.Beeping.NPcoNP.Source284PolynomialGuardFamily
import Shared.ComplexityBridge.FiniteVerifierCompiler
import Shared.Codes.FiniteProgramRepair

/-! An actual canonical polynomial-time tagged verifier for every canonical
polynomial-time pair relation. Witness limits are computed from the parsed
source prefix and the original cutoff is enforced on every input. This does
not yet load the verifier from the source's two unbounded tape halves. -/
namespace Shared.Beeping.NPcoNP.Source284CanonicalTaggedVerifier

open ComplexityTheory Shared.ComplexityBridge
open Shared.Codes.FinitePrograms
open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284RawParse (payload)

/-- The source prefix is parsed before its polynomial witness budget is
computed; the complete pair is charged by the canonical input encoding. -/
def compare (p : Polynomial Nat) (R : List Bool × List Bool → Bool)
    (v : List Bool × List Bool) : Bool :=
  Source284TaggedBitDecode.check R
    (TM2UnaryPolynomialIO.unaryPolynomial p (Source284PolynomialGuardFamily.stretch (payload v.1)),v)

theorem compare_isPolyTime (p : Polynomial Nat) (R : List Bool × List Bool → Bool)
    (hR : IsPolyTime R) : IsPolyTime (compare p R) := by
  let input : List Bool × List Bool → List Bool := fun v => v.1
  let parsed : List Bool × List Bool → List Bool := fun v => payload (input v)
  let stretched : List Bool × List Bool → List Bool := fun v => Source284PolynomialGuardFamily.stretch (parsed v)
  let tokens : List Bool × List Bool → List Bool := fun v => TM2UnaryPolynomialIO.unaryPolynomial p (stretched v)
  have hi : IsPolyTime input := TM2PairFirst.first_isPolyTime
  have hp : IsPolyTime parsed := TM2Compose.isPolyTime_comp input payload hi Source284RawParseTM2.payload_isPolyTime
  have hs : IsPolyTime stretched := TM2Compose.isPolyTime_comp parsed Source284PolynomialGuardFamily.stretch
    hp Source284PolynomialGuardFamily.stretch_isPolyTime
  have ht : IsPolyTime tokens := TM2Compose.isPolyTime_comp stretched (TM2UnaryPolynomialIO.unaryPolynomial p)
    hs (TM2UnaryPolynomialIO.unaryPolynomial_isPolyTime p)
  have hid : IsPolyTime (id : (List Bool × List Bool) → (List Bool × List Bool)) :=
    ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  exact TM2Compose.isPolyTime_comp (fun v : List Bool × List Bool => (tokens v,v))
    (Source284TaggedBitDecode.check R) (TM2GuardAllStep.pair_isPolyTime tokens id ht hid)
    (Source284TaggedBitDecode.check_isPolyTime R hR)

/-- The executable checker uses exactly the original normalized witness
limit, including malformed tags, empty inputs, high aliases and virtual zeros. -/
theorem compare_correct (p : Polynomial Nat) (R : List Bool × List Bool → Bool)
    (input cert : List Bool) :
    compare p R (input,cert) = Source284TaggedWitnessCodec.check
      (p.eval (2*Source284Parser.length (value input)+1)) (fun w => R (payload input,w)) (value cert) := by
  rw [compare,Source284TaggedBitDecode.check_correct]
  simp [TM2UnaryPolynomialIO.unaryPolynomial,Source284PolynomialGuardFamily.stretch,
    Source284RawParse.parse_length,Nat.add_assoc,show 2*(payload input).length =
      (payload input).length+(payload input).length by omega]

/-- There is one valid finite table, independent of both input lists, with a
polynomial clock measured on the complete canonical pair encoding. -/
theorem finite_program (p : Polynomial Nat) (R : List Bool × List Bool → Bool)
    (hR : IsPolyTime R) :
    ∃ (program : Program) (clock : Polynomial Nat), valid program = true ∧ ∀ input cert,
      bounded program (BitstringEncoding.bitEncode (input,cert))
        (clock.eval (BitstringEncoding.bitEncode (input,cert)).length) = some (compare p R (input,cert)) := by
  obtain ⟨program,clock,hcorrect⟩ := FiniteVerifierCompiler.canonical_finite_verifier_compiler
    (compare p R) (compare_isPolyTime p R hR)
  refine ⟨Shared.Codes.FiniteProgramRepair.repair program,clock,
    Shared.Codes.FiniteProgramRepair.repair_valid program,?_⟩
  intro input cert
  rw [Shared.Codes.FiniteProgramRepair.bounded_repair]
  exact hcorrect input cert

end Shared.Beeping.NPcoNP.Source284CanonicalTaggedVerifier
