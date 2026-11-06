import Shared.ComplexityBridge.TM2BinaryListLength
import Shared.ComplexityBridge.CircuitSelect

/-! Finite polynomial-time construction of gates and one concrete mux,
using the shared explicit gate bitstring encoding. -/
namespace Shared.ComplexityBridge.TM2GateConstruct
open Shared.ComplexityBridge
open Shared.ComplexityBridge.CircuitCNF
open Shared.ComplexityBridge.TM2GateEncoding

/-- Reuse a finite tuple-producing machine when its output bits are exactly
the shared encoding of the desired gate. -/
theorem gate_of_code {α : Type} [BitstringEncoding α] (F : α → Gate) (C : α → Code)
    (hC : ComplexityTheory.IsPolyTime C) (hcode : ∀ x, encode (F x) = C x) :
    ComplexityTheory.IsPolyTime F := by
  obtain ⟨m⟩ := hC
  refine ⟨{ toTM2ComputableAux := m.toTM2ComputableAux, time := m.time, outputsFun := ?_ }⟩
  intro x
  have hr := m.outputsFun x
  have he : BitstringEncoding.bitEncode (F x) = BitstringEncoding.bitEncode (C x) := by
    rw [encode_bits,hcode]
  change Turing.TM2OutputsInTime m.tm
    ((BitstringEncoding.bitEncode x).map m.inputAlphabet.symm)
    (some ((BitstringEncoding.bitEncode (F x)).map m.outputAlphabet.symm))
    (m.time.eval (BitstringEncoding.bitEncode x).length)
  rw [he]
  exact hr

def tagged (a b : Bool) (p : Bool × (Nat × Nat)) : Code := ((a,b),p)

theorem tagged_isPolyTime (a b : Bool) : ComplexityTheory.IsPolyTime (tagged a b) := by
  let fa : Bool × (Nat × Nat) → Bool := fun _ => a
  let fb : Bool × (Nat × Nat) → Bool := fun _ => b
  let tag : Bool × (Nat × Nat) → Bool × Bool := fun x => (fa x,fb x)
  have ha : ComplexityTheory.IsPolyTime fa := TM2Constant.isPolyTime a
  have hb : ComplexityTheory.IsPolyTime fb := TM2Constant.isPolyTime b
  have ht : ComplexityTheory.IsPolyTime tag := TM2GuardAllStep.pair_isPolyTime fa fb ha hb
  have hi : ComplexityTheory.IsPolyTime (id : Bool × (Nat × Nat) → Bool × (Nat × Nat)) :=
    ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  exact TM2GuardAllStep.pair_isPolyTime tag id ht hi

theorem neg_isPolyTime : ComplexityTheory.IsPolyTime Gate.neg := by
  let zero : Nat → Nat := fun _ => 0
  let falsity : Nat → Bool := fun _ => false
  let coords : Nat → Nat × Nat := fun n => (n,zero n)
  let payload : Nat → Bool × (Nat × Nat) := fun n => (falsity n,coords n)
  let code : Nat → Code := fun n => tagged false true (payload n)
  have hz : ComplexityTheory.IsPolyTime zero := TM2EmptyConstant.zero_isPolyTime
  have hf : ComplexityTheory.IsPolyTime falsity := TM2Constant.isPolyTime false
  have hi : ComplexityTheory.IsPolyTime (id : Nat → Nat) := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have hc : ComplexityTheory.IsPolyTime coords := TM2GuardAllStep.pair_isPolyTime id zero hi hz
  have hp : ComplexityTheory.IsPolyTime payload := TM2GuardAllStep.pair_isPolyTime falsity coords hf hc
  have hcode : ComplexityTheory.IsPolyTime code := TM2Compose.isPolyTime_comp payload (tagged false true) hp (tagged_isPolyTime false true)
  exact gate_of_code Gate.neg code hcode (fun _ => rfl)

theorem binary_isPolyTime (conjunction : Bool) : ComplexityTheory.IsPolyTime
    (fun p : Nat × Nat => if conjunction then Gate.conj p.1 p.2 else Gate.disj p.1 p.2) := by
  let falsity : Nat × Nat → Bool := fun _ => false
  let payload : Nat × Nat → Bool × (Nat × Nat) := fun p => (falsity p,p)
  let code : Nat × Nat → Code := fun p => tagged true (!conjunction) (payload p)
  have hf : ComplexityTheory.IsPolyTime falsity := TM2Constant.isPolyTime false
  have hi : ComplexityTheory.IsPolyTime (id : Nat × Nat → Nat × Nat) := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have hp : ComplexityTheory.IsPolyTime payload := TM2GuardAllStep.pair_isPolyTime falsity id hf hi
  have hcode : ComplexityTheory.IsPolyTime code := TM2Compose.isPolyTime_comp payload (tagged true (!conjunction)) hp (tagged_isPolyTime true (!conjunction))
  apply gate_of_code _ code hcode
  intro p
  cases conjunction <;> rfl

theorem conj_isPolyTime : ComplexityTheory.IsPolyTime (fun p : Nat × Nat => Gate.conj p.1 p.2) :=
  binary_isPolyTime true

theorem disj_isPolyTime : ComplexityTheory.IsPolyTime (fun p : Nat × Nat => Gate.disj p.1 p.2) :=
  binary_isPolyTime false

abbrev MuxInput := Nat × (Nat × (Nat × Nat))
def mux (p : MuxInput) : List Gate := CircuitSelect.mux p.1 p.2.1 p.2.2.1 p.2.2.2

/-- All four gates of a mux, including binary offset increments, are built by
finite machines with charged canonical encodings. -/
theorem mux_isPolyTime : ComplexityTheory.IsPolyTime mux := by
  let base : MuxInput → Nat := fun p => p.1
  let rest : MuxInput → Nat × (Nat × Nat) := fun p => p.2
  let sel : MuxInput → Nat := fun p => p.2.1
  let pair : MuxInput → Nat × Nat := fun p => p.2.2
  let yes : MuxInput → Nat := fun p => p.2.2.1
  let no : MuxInput → Nat := fun p => p.2.2.2
  let one : MuxInput → Nat := fun p => base p+1
  let two : MuxInput → Nat := fun p => base p+2
  let g0 : MuxInput → Gate := fun p => Gate.neg (sel p)
  let g1 : MuxInput → Gate := fun p => Gate.conj (sel p) (yes p)
  let g2 : MuxInput → Gate := fun p => Gate.conj (base p) (no p)
  let g3 : MuxInput → Gate := fun p => Gate.disj (one p) (two p)
  have hb : ComplexityTheory.IsPolyTime base := TM2PairFirst.first_isPolyTime
  have hr : ComplexityTheory.IsPolyTime rest := TM2GuardAllStep.second_isPolyTime
  have hs : ComplexityTheory.IsPolyTime sel := TM2Compose.isPolyTime_comp rest (fun p : Nat × (Nat × Nat) => p.1) hr TM2PairFirst.first_isPolyTime
  have hp : ComplexityTheory.IsPolyTime pair := TM2Compose.isPolyTime_comp rest (fun p : Nat × (Nat × Nat) => p.2) hr TM2GuardAllStep.second_isPolyTime
  have hy : ComplexityTheory.IsPolyTime yes := TM2Compose.isPolyTime_comp pair (fun p : Nat × Nat => p.1) hp TM2PairFirst.first_isPolyTime
  have hn : ComplexityTheory.IsPolyTime no := TM2Compose.isPolyTime_comp pair (fun p : Nat × Nat => p.2) hp TM2GuardAllStep.second_isPolyTime
  have h1 : ComplexityTheory.IsPolyTime one := TM2Compose.isPolyTime_comp base Nat.succ hb CNFBinaryIncrement.successor_isPolyTime
  have h2 : ComplexityTheory.IsPolyTime two := TM2Compose.isPolyTime_comp base (fun n => n+2) hb TM2ShapeClauses.plusTwo_isPolyTime
  have hg0 : ComplexityTheory.IsPolyTime g0 := TM2Compose.isPolyTime_comp sel Gate.neg hs neg_isPolyTime
  have hg1 : ComplexityTheory.IsPolyTime g1 := TM2Compose.isPolyTime_comp (fun p => (sel p,yes p))
    (fun p : Nat × Nat => Gate.conj p.1 p.2) (TM2GuardAllStep.pair_isPolyTime sel yes hs hy) conj_isPolyTime
  have hg2 : ComplexityTheory.IsPolyTime g2 := TM2Compose.isPolyTime_comp (fun p => (base p,no p))
    (fun p : Nat × Nat => Gate.conj p.1 p.2) (TM2GuardAllStep.pair_isPolyTime base no hb hn) conj_isPolyTime
  have hg3 : ComplexityTheory.IsPolyTime g3 := TM2Compose.isPolyTime_comp (fun p => (one p,two p))
    (fun p : Nat × Nat => Gate.disj p.1 p.2) (TM2GuardAllStep.pair_isPolyTime one two h1 h2) disj_isPolyTime
  let tail : MuxInput → List Gate := fun p => [g1 p,g2 p,g3 p]
  have htail : ComplexityTheory.IsPolyTime tail := TM2GateCNFPieces.tripleList_isPolyTime g1 g2 g3 hg1 hg2 hg3
  have hargs := TM2GuardAllStep.pair_isPolyTime g0 tail hg0 htail
  have h := TM2Compose.isPolyTime_comp (fun p => (g0 p,tail p)) (TM2ListAppend.cons (α := Gate)) hargs TM2ListAppend.cons_isPolyTime
  have he : (fun p => TM2ListAppend.cons (g0 p,tail p)) = mux := by
    funext p
    rfl
  rw [he] at h
  exact h

namespace Fixtures
example : mux (5,1,2,3) = [.neg 1,.conj 1 2,.conj 5 3,.disj 6 7] := rfl
end Fixtures
end Shared.ComplexityBridge.TM2GateConstruct
