import Shared.ComplexityBridge.CNFEncodingComputability
import Mathlib.Data.Nat.Bits
import Shared.ComplexityBridge.TM2ListCodec
set_option maxHeartbeats 3000000

/-! The number encoding used for CNF identifiers. Binary-list operations are
charged explicitly; this is a component of the generator, not a complete
machine-time proof. -/
namespace Shared.ComplexityBridge.CNFNatBitCosts
open Shared.ComplexityBridge.CNFEncodingComputability

/-- The prior numeric extraction loop needs only the binary width as fuel.
The proof counts loop iterations, not the machine cost of `Nat.div2`. -/
theorem bitLoop_binary_width (n : Nat) (acc : List Bool) :
    bitLoop n.bits.length (n,acc) = (0,n.bits.reverse ++ acc) := by
  induction n using Nat.strong_induction_on generalizing acc with
  | h n ih =>
    by_cases hn : n = 0
    · subst n; simp [bitLoop]
    · have hlen : n.bits.length = n.div2.bits.length+1 := by
        rw [bits_unfold n hn]
        simp
      have hlt : n.div2 < n := Nat.binaryRec_decreasing hn
      rw [hlen,bitLoop,Function.iterate_succ_apply,bitStep,if_neg hn]
      change bitLoop n.div2.bits.length (n.div2,n.bodd::acc) = _
      rw [ih n.div2 hlt (n.bodd::acc),bits_unfold n hn]
      simp [List.reverse_cons,List.append_assoc]

/-- One pass over a least-significant-bit-first list writes it in reverse
order, charging one bit read and one bit write per element. -/
def reverseCopy : List Bool → List Bool → List Bool × Nat
  | [], acc => (acc,1)
  | b::bs, acc =>
      let r := reverseCopy bs (b::acc)
      (r.1,r.2+2)

theorem reverseCopy_correct (bits acc : List Bool) :
    reverseCopy bits acc = (bits.reverse++acc,2*bits.length+1) := by
  induction bits generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    simp [reverseCopy,ih,List.reverse_cons,List.append_assoc]
    omega

/-- Given a binary representation as tape bits, no unary loop or unbounded
integer operation is needed to emit the pinned natural-number encoding.
The reverse-oriented output matches the usual stack-writing convention. -/
theorem encodeNat_reverse_from_bits (n : Nat) (acc : List Bool) :
    reverseCopy n.bits acc =
      ((BitstringEncoding.bitEncode n).reverse++acc,2*n.bits.length+1) := by
  change reverseCopy n.bits acc = ((Computability.encodeNat n).reverse++acc,2*n.bits.length+1)
  rw [encodeNat_bits]
  exact reverseCopy_correct n.bits acc


/-- The existing finite TM2 routine performs this reverse copy from its
    explicit scratch-stack boundary in exactly one statement block per bit
    plus one final cleanup block. Initialization of that boundary is separate. -/
theorem reverseCopy_tm2 (bits acc : List Bool) (v : Option Bool) :
    Shared.ComplexityBridge.TM2Symbols.runSteps
      Shared.ComplexityBridge.TM2ListCodec.Decode.machine.step (bits.length+1)
      (Shared.ComplexityBridge.TM2ListCodec.Decode.cfg .restore v [] bits acc) =
      some (Turing.haltList Shared.ComplexityBridge.TM2ListCodec.Decode.machine (reverseCopy bits acc).1) := by
  rw [reverseCopy_correct]
  exact Shared.ComplexityBridge.TM2ListCodec.Decode.restore_run bits acc v

namespace Fixtures
example : reverseCopy [] [] = ([],1) := rfl
example : reverseCopy [true,false,true,true] [] = ([true,true,false,true],9) := by decide
example : bitLoop (13 : Nat).bits.length (13,[]) = (0,[true,true,false,true]) := by decide
end Fixtures

end Shared.ComplexityBridge.CNFNatBitCosts
