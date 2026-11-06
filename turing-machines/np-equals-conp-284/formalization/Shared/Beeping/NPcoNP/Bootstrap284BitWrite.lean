import Shared.Beeping.NPcoNP.Bootstrap284BitSnapshot

/-! A verified bit-level write for packed bootstrap snapshots. This is one
primitive for a future packed executor, not a correctness claim for one. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284BitWrite
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.Bootstrap284BitSnapshot

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- Toggle the selected bit only when it differs from the requested value. -/
def bitPut (bits index : Nat) (value : Bool) : Nat :=
  if bits.testBit index=value then bits else bits ^^^ (2^index)

/-- The operation changes exactly the selected bit. -/
theorem testBit_bitPut (bits index j : Nat) (value : Bool) :
    (bitPut bits index value).testBit j = if j=index then value else bits.testBit j := by
  by_cases he : bits.testBit index=value
  · simp [bitPut,he]
    intro hj
    subst j
    exact he
  · by_cases hj : j=index
    · subst j
      simp only [bitPut,if_neg he, Nat.testBit_xor,Nat.testBit_two_pow,decide_true,if_true]
      cases hv : bits.testBit index <;> cases value <;> simp_all
    · simp [bitPut,he,Nat.testBit_xor,Nat.testBit_two_pow,hj,Ne.symm hj]

/-- Writing a cell within the declared span agrees pointwise with writing to
the unbounded tape represented by the snapshot. -/
theorem snapshot_bitPut (base h : Int) (span bits : Nat) (value : Bool)
    (hh : base≤h ∧ h<base+(span : Int)) :
    bitSnapshot base span (bitPut bits (h-base).toNat value) =
      put (bitSnapshot base span bits) h value := by
  funext p
  by_cases hp : base≤p ∧ p<base+(span : Int)
  · have hp' : (((p-base).toNat : Nat) : Int)=p-base := Int.toNat_of_nonneg (by omega)
    have hh' : (((h-base).toNat : Nat) : Int)=h-base := Int.toNat_of_nonneg (by omega)
    have he : (p-base).toNat=(h-base).toNat ↔ p=h := by
      constructor
      · intro hv
        have hvi := congrArg (fun x : Nat => (x : Int)) hv
        omega
      · intro hv; subst p; rfl
    simp only [bitSnapshot,if_pos hp,testBit_bitPut,put,he]
  · have hne : p≠h := by omega
    simp [bitSnapshot,hp,put,hne]

end Shared.Beeping.NPcoNP.Bootstrap284BitWrite
