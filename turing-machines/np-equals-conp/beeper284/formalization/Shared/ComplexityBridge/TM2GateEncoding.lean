import Shared.ComplexityBridge.TM2GateCNFPieces

/-! A finite, explicit gate serialization for the circuit-to-CNF layer.
The tag and payload use the frozen Google Boolean, natural and pair encodings.
Unused payload fields are ignored by decoding; emitted gate codes use zero
in those fields. -/
namespace Shared.ComplexityBridge.TM2GateEncoding
open Shared.ComplexityBridge.CircuitCNF

abbrev Code := (Bool × Bool) × (Bool × (Nat × Nat))

def encode : Gate → Code
  | .constant b => ((false,false),(b,(0,0)))
  | .neg x => ((false,true),(false,(x,0)))
  | .conj x y => ((true,false),(false,(x,y)))
  | .disj x y => ((true,true),(false,(x,y)))

def decode (c : Code) : Gate :=
  match c.1 with
  | (false,false) => .constant c.2.1
  | (false,true) => .neg c.2.2.1
  | (true,false) => .conj c.2.2.1 c.2.2.2
  | (true,true) => .disj c.2.2.1 c.2.2.2

theorem decode_encode (g : Gate) : decode (encode g) = g := by cases g <;> rfl

/-- Gate encoding is transported from the explicit, already encoded tuple. -/
instance gateBitstringEncoding : BitstringEncoding Gate :=
  BitstringEncoding.ofLeftInverse encode (fun c => some (decode c)) (fun g => by simp [decode_encode])

theorem encode_bits (g : Gate) : BitstringEncoding.bitEncode g = BitstringEncoding.bitEncode (encode g) := rfl

theorem encode_injective : Function.Injective encode := by
  intro a b h
  have := congrArg decode h
  simpa [decode_encode] using this

/-- The new gate encoding is faithful and has a total decoding function;
malformed bitstrings follow the underlying tuple decoder's `Option` behavior. -/
theorem gate_bit_roundtrip (g : Gate) : BitstringEncoding.bitDecode (BitstringEncoding.bitEncode g) = some g :=
  BitstringEncoding.bitDecode_bitEncode g

end Shared.ComplexityBridge.TM2GateEncoding
