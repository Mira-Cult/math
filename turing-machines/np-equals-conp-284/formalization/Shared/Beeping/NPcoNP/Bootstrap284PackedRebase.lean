import Shared.Beeping.NPcoNP.Bootstrap284PackedScans

/-! Widen a packed representation to the left without changing any physical
configuration. Repacking is a proof-side representation change, not a machine
transition. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284PackedRebase
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Bootstrap284BitSnapshot
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- Shift the packed bits when extending the declared span to the left. -/
def extendLeft (delta : Nat) (c : Packed) : Packed := {c with bits := c.bits <<< delta}

/-- A wider packed snapshot is pointwise equal to the old snapshot on the
entire integer tape, including the newly admitted left-hand cells. -/
theorem snapshot_extendLeft (base : Int) (span bits delta : Nat) :
    bitSnapshot (base-(delta : Int)) (span+delta) (bits <<< delta) =
      bitSnapshot base span bits := by
  funext p
  have hend : base-(delta : Int)+((span+delta : Nat) : Int)=base+(span : Int) := by
    push_cast; omega
  by_cases hp : base≤p ∧ p<base+(span : Int)
  · have hp' : base-(delta : Int)≤p ∧ p<base-(delta : Int)+((span+delta : Nat) : Int) := by
      rw [hend]; omega
    have ha : (((p-base).toNat : Nat) : Int)=p-base := Int.toNat_of_nonneg (by omega)
    have hb : (((p-(base-(delta : Int))).toNat : Nat) : Int)=p-(base-(delta : Int)) := Int.toNat_of_nonneg (by omega)
    have hi : (p-(base-(delta : Int))).toNat=(p-base).toNat+delta := by omega
    simp only [bitSnapshot,if_pos hp,if_pos hp',Nat.testBit_shiftLeft,hi]
    simp
  · by_cases hp' : base-(delta : Int)≤p ∧ p<base-(delta : Int)+((span+delta : Nat) : Int)
    · have hlow : p<base := by rw [hend] at hp'; omega
      have hb : (((p-(base-(delta : Int))).toNat : Nat) : Int)=p-(base-(delta : Int)) := Int.toNat_of_nonneg (by omega)
      have hi : (p-(base-(delta : Int))).toNat<delta := by omega
      simp [bitSnapshot,hp,hp',Nat.testBit_shiftLeft,show ¬ delta≤(p-(base-(delta : Int))).toNat by omega]
    · simp only [bitSnapshot,if_neg hp,if_neg hp']

/-- Repacking does not change the complete configuration or insert any
physical machine step. -/
theorem toConfig_extendLeft (base : Int) (span delta : Nat) (c : Packed) :
    toConfig (base-(delta : Int)) (span+delta) (extendLeft delta c)=toConfig base span c := by
  simp only [toConfig,extendLeft,snapshot_extendLeft]

end Shared.Beeping.NPcoNP.Bootstrap284PackedRebase
