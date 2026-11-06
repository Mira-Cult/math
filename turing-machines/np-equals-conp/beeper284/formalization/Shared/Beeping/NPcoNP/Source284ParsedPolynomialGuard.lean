import Shared.Beeping.NPcoNP.Source284PolynomialGuardCheckTM2
import Shared.Beeping.NPcoNP.Source284RawParseTM2

/-! End-to-end canonical TM2 execution of the generated guard family, with
its bound derived by the actual raw-list source parser. This still generates
an input-dependent table and does not construct a fixed source controller. -/
namespace Shared.Beeping.NPcoNP.Source284ParsedPolynomialGuard

open ComplexityTheory Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284PolynomialGuardFamily
open Shared.Codes.BitNumeralCompare (value)

abbrev Input := EncRows × (List Bool × List Bool)

def prepare (x : Input) : Source284PolynomialGuardCheckTM2.Input :=
  ((Source284RawParse.payload x.2.1,x.1),x.2)

theorem prepare_isPolyTime : IsPolyTime prepare := by
  let original : Input → EncRows := fun x => x.1
  let tapes : Input → List Bool × List Bool := fun x => x.2
  let input : Input → List Bool := fun x => (tapes x).1
  let payload : Input → List Bool := fun x => Source284RawParse.payload (input x)
  have ho : IsPolyTime original := TM2PairFirst.first_isPolyTime
  have ht : IsPolyTime tapes := TM2GuardAllStep.second_isPolyTime
  have hi : IsPolyTime input := TM2Compose.isPolyTime_comp tapes _ ht TM2PairFirst.first_isPolyTime
  have hp : IsPolyTime payload := TM2Compose.isPolyTime_comp input _ hi Source284RawParseTM2.payload_isPolyTime
  exact TM2GuardAllStep.pair_isPolyTime (fun x => (payload x,original x)) tapes
    (TM2GuardAllStep.pair_isPolyTime payload original hp ho) ht

def check (p time : Polynomial Nat) (x : Input) : Bool :=
  Source284PolynomialGuardCheckTM2.check p time (prepare x)

theorem check_isPolyTime (p time : Polynomial Nat) : IsPolyTime (check p time) :=
  TM2Compose.isPolyTime_comp prepare (Source284PolynomialGuardCheckTM2.check p time)
    prepare_isPolyTime (Source284PolynomialGuardCheckTM2.check_isPolyTime p time)

theorem check_empty (p time : Polynomial Nat) (x : Input)
    (hi : Source284Parser.length (value x.2.1) = 0) : check p time x = true := by
  exact Source284PolynomialGuardCheckTM2.check_empty p time (prepare x) hi

/-- One executable comparison on a positive input, with the parsed witness
bound and the original verifier's finite cutoff. -/
theorem check_positive (p time : Polynomial Nat) (x : Input) (predicate : List Bool → Bool)
    (hi : 0 < Source284Parser.length (value x.2.1))
    (hn : 0 < x.1.length) (hv : Source284ListTables.valid (decodeRows x.1) = true)
    (hmatch : ∀ c w, Source284TaggedWitnessCodec.decode
        (p.eval (2*Source284Parser.length (value x.2.1)+1)) c = some w →
      (run (Source284ListTables.table (decodeRows x.1)) ⟨c,value x.2.1,some 0⟩
        (time.eval (Source284Parser.length (value x.2.1))+1)).state.isNone = predicate w) :
    check p time x = Source284TaggedWitnessCodec.check
      (p.eval (2*Source284Parser.length (value x.2.1)+1)) predicate (value x.2.2) := by
  have hm : ∀ c w, Source284TaggedWitnessCodec.decode (limit p (prepare x).1) c = some w →
      (run (Source284ListTables.table (decodeRows (prepare x).1.2))
        ⟨c,value (prepare x).2.1,some 0⟩ (fuel time (prepare x).1+1)).state.isNone = predicate w := by
    simpa only [prepare,limit,fuel,Source284RawParse.parse_length] using hmatch
  have h := Source284PolynomialGuardCheckTM2.check_positive p time (prepare x) predicate hi hn hv hm
  simpa only [check,prepare,limit,Source284RawParse.parse_length] using h

/-- Certificate search agrees with a verifier predicate at the original
polynomial witness bound, now expressed using the actual source parser.
The verifier correctness hypothesis must cover every tagged alias. -/
theorem check_bounded_search (p time : Polynomial Nat) (original : EncRows) (input : List Bool)
    (predicate : List Bool → Bool) (hi : 0 < Source284Parser.length (value input))
    (hn : 0 < original.length) (hv : Source284ListTables.valid (decodeRows original) = true)
    (hmatch : ∀ c w, Source284TaggedWitnessCodec.decode
        (p.eval (2*Source284Parser.length (value input)+1)) c = some w →
      (run (Source284ListTables.table (decodeRows original)) ⟨c,value input,some 0⟩
        (time.eval (Source284Parser.length (value input))+1)).state.isNone = predicate w) :
    (∃ cert : List Bool,
      value cert < 2^(cutoff p time (Source284RawParse.payload input,original)) ∧
      check p time (original,(input,cert)) = true) ↔
      ∃ w, w.length ≤ p.eval (2*Source284Parser.length (value input)+1) ∧ predicate w = true := by
  have h := Source284PolynomialGuardCheckTM2.check_bounded_search p time
    (Source284RawParse.payload input,original) input predicate hi hn hv
    (by simpa only [limit,fuel,Source284RawParse.parse_length] using hmatch)
  simpa only [check,prepare,limit,Source284RawParse.parse_length] using h

namespace Fixtures

example (p time : Polynomial Nat) (cert : List Bool) :
    check p time ([],([],cert)) = true := by
  apply check_empty
  change Source284Parser.length (value ([] : List Bool)) = 0
  decide +kernel

example : Source284Parser.length (value [true]) = 1 := by decide +kernel

end Fixtures

end Shared.Beeping.NPcoNP.Source284ParsedPolynomialGuard
