import Shared.Beeping.NPcoNP.Source284PackedGuardCompiler
import Shared.Beeping.NPcoNP.Source284HardnessFrame

/-! Bounded canonical pair data for the fixed packed verifier. These are
mathematical normalization lemmas; a finite source loader that performs the
normalization from the original two tape halves is still an obligation. -/
namespace Shared.Beeping.NPcoNP.Source284PackedGuardWindow

open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284Parser (frameBits)
open Shared.Beeping.NPcoNP.Source284WitnessWindow (width)
open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284TableRun

/-- The two tag bits and original witness window are exactly the relevant
low bits; all higher certificate bits are aliases. -/
theorem tagged_decode_mod (m certificate : Nat) :
    Source284TaggedWitnessCodec.decode m (certificate % 2^(width m+2)) =
      Source284TaggedWitnessCodec.decode m certificate := by
  have hp : 2^(width m+2) = 4*2^(width m) := by
    simp only [Nat.pow_add, show 2^2 = 4 by decide]
    omega
  have hmod : (certificate % 2^(width m+2)) % 4 = certificate % 4 := by
    apply Nat.mod_mod_of_dvd
    rw [hp]
    exact ⟨2^(width m), by omega⟩
  have hdiv : (certificate % 2^(width m+2))/4 = (certificate/4) % 2^(width m) := by
    rw [hp]
    exact Nat.mod_mul_right_div_self certificate 4 (2^(width m))
  simp only [Source284TaggedWitnessCodec.decode,hmod,hdiv,Source284WitnessWindow.decode_mod]

theorem tagged_check_mod (m certificate : Nat) (predicate : List Bool → Bool) :
    Source284TaggedWitnessCodec.check m predicate (certificate % 2^(width m+2)) =
      Source284TaggedWitnessCodec.check m predicate certificate := by
  simp only [Source284TaggedWitnessCodec.check,tagged_decode_mod]

def inputBits (input : List Bool) : List Bool :=
  frameBits (Source284RawParse.payload input) [true]

def certificateBits (m certificate : Nat) : List Bool :=
  (certificate % 2^(width m+2)).bits

theorem input_payload (input : List Bool) :
    Source284RawParse.payload (inputBits input) = Source284RawParse.payload input :=
  Source284WitnessWindow.payload_frame _

theorem input_prefix_length (input : List Bool) :
    Source284Parser.length (value (inputBits input)) = Source284Parser.length (value input) := by
  rw [Source284RawParse.parse_length,Source284RawParse.parse_length,input_payload]

theorem inputBits_length (input : List Bool) :
    (inputBits input).length = 2*Source284Parser.length (value input)+2 := by
  simp [inputBits,Source284HardnessFrame.frameBits_length,Source284RawParse.parse_length]

theorem certificateBits_value (m certificate : Nat) :
    value (certificateBits m certificate) = certificate % 2^(width m+2) := by
  simp [certificateBits,Shared.Codes.BinaryAdditionCanonical.value_bits]

theorem certificateBits_length (m certificate : Nat) :
    (certificateBits m certificate).length ≤ width m+2 := by
  rw [certificateBits,Nat.size_eq_bits_len,Nat.size_le]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- The packed canonical input has a bound independent of all discarded
suffix and high-certificate bits. `m` remains the original witness limit. -/
theorem packed_length (m certificate : Nat) (input : List Bool) :
    (BitstringEncoding.bitEncode (inputBits input,certificateBits m certificate)).length ≤
      12*Source284Parser.length (value input)+6*m+25 := by
  rw [Source284PackedGuardCompiler.pair_encoded_length,inputBits_length]
  have hc := certificateBits_length m certificate
  simp only [Source284WitnessWindow.width] at hc
  omega

theorem inputBits_canonical (input : List Bool) :
    (value (inputBits input)).bits = inputBits input :=
  Shared.Codes.BinaryAdditionCanonical.canonical_value_bits
    (Source284WitnessWindow.canonical_frame _)

theorem inputBits_payload (input : List Bool) :
    Source284RawParse.payload (value (inputBits input)).bits = Source284RawParse.payload input := by
  rw [inputBits_canonical,input_payload]

/-- A fixed source program on a normalized packed input needs only a
polynomial clock in the source prefix length. Constructing the normalization
on the original two source tape halves remains a separate loader obligation. -/
theorem source_machine_normalized (p time : Polynomial Nat) (original : EncRows)
    (R : List Bool × List Bool → Bool)
    (hn : 0 < original.length) (hv : Source284ListTables.valid (decodeRows original) = true)
    (hmatch : ∀ i : Nat, 0 < Source284Parser.length i → ∀ c w,
      Source284TaggedWitnessCodec.decode (p.eval (2*Source284Parser.length i+1)) c = some w →
      (Source284TableRun.run (Source284ListTables.table (decodeRows original))
        ⟨c,i,some 0⟩ (time.eval (Source284Parser.length i)+1)).state.isNone =
          R (Source284RawParse.payload i.bits,w)) :
    ∃ (program : Shared.Codes.FinitePrograms.Program) (clock : Polynomial Nat),
      Shared.Codes.FinitePrograms.valid program = true ∧ ∀ (input : List Bool) (certificate : Nat),
      0 < Source284Parser.length (value input) →
      Source284Relative.accepts (Source284CompileRecords.compile program)
        (value (BitstringEncoding.bitEncode
          (inputBits input,certificateBits (p.eval (2*Source284Parser.length (value input)+1)) certificate))) 0
        (clock.eval (Source284Parser.length (value input))) =
      Source284TaggedWitnessCodec.check (p.eval (2*Source284Parser.length (value input)+1))
        (fun w => R (Source284RawParse.payload input,w)) certificate := by
  obtain ⟨program,q,hvprog,hsource⟩ :=
    Source284PackedGuardCompiler.source_machine_positive p time original hn hv
  let bound : Polynomial Nat := Polynomial.C 12 * Polynomial.X +
    Polynomial.C 6 * p.comp (Polynomial.C 2 * Polynomial.X + Polynomial.C 1) + Polynomial.C 25
  let clock : Polynomial Nat := q.comp bound
  refine ⟨program,clock,hvprog,?_⟩
  intro input certificate hi
  let m := p.eval (2*Source284Parser.length (value input)+1)
  let packed := BitstringEncoding.bitEncode (inputBits input,certificateBits m certificate)
  have hlen : packed.length ≤ bound.eval (Source284Parser.length (value input)) := by
    have hp := packed_length m certificate input
    simpa [packed,bound,m,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_comp,
      Polynomial.eval_C,Polynomial.eval_X] using hp
  have hclock : q.eval packed.length ≤ clock.eval (Source284Parser.length (value input)) := by
    simp only [clock,Polynomial.eval_comp]
    exact Shared.ComplexityBridge.TM2Compose.polynomial_eval_mono q hlen
  let extra := clock.eval (Source284Parser.length (value input))-q.eval packed.length
  have hextra : q.eval packed.length+extra = clock.eval (Source284Parser.length (value input)) := by
    dsimp [extra]; omega
  have hi' : 0 < Source284Parser.length (value (inputBits input)) := by
    rw [input_prefix_length]; exact hi
  have hm : ∀ c w, Source284TaggedWitnessCodec.decode
      (p.eval (2*Source284Parser.length (value (inputBits input))+1)) c = some w →
      (Source284TableRun.run (Source284ListTables.table (decodeRows original))
        ⟨c,value (inputBits input),some 0⟩
        (time.eval (Source284Parser.length (value (inputBits input)))+1)).state.isNone =
          R (Source284RawParse.payload input,w) := by
    intro c w hw
    have h := hmatch (value (inputBits input)) hi' c w hw
    simpa only [inputBits_payload] using h
  have hs := hsource (inputBits input) (certificateBits m certificate) extra
    (fun w => R (Source284RawParse.payload input,w)) hi' hm
  change Source284Relative.accepts (Source284CompileRecords.compile program) (value packed) 0
    (q.eval packed.length+extra) = _ at hs
  rw [hextra,input_prefix_length,certificateBits_value,tagged_check_mod] at hs
  exact hs

namespace Fixtures
example : Source284TaggedWitnessCodec.decode 0 0 = Source284TaggedWitnessCodec.decode 0 16 := by decide +kernel
example : inputBits [true] = [true,false,false,true] := by decide +kernel
example : (certificateBits 0 255).length ≤ 4 := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284PackedGuardWindow
