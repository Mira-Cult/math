import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S087C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13557)) 183762989 183795757 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 183762989 183795757).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13557 183762989 183795757
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13558)) 183795757 183828525 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 183795757 183828525).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13558 183795757 183828525
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13559)) 183828525 183861293 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 183828525 183861293).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13559 183828525 183861293
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13560)) 183861293 183894061 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 183861293 183894061).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13560 183861293 183894061
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 183762989 183828525).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 183762989 ≤ 183795757)
    (by decide : 183795757 ≤ 183828525) block0 block1

theorem join_0_1 : (twinPrimeSegment 183828525 183894061).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 183828525 ≤ 183861293)
    (by decide : 183861293 ≤ 183894061) block2 block3

theorem join_1_0 : (twinPrimeSegment 183762989 183894061).card = 448 := by
  simpa using combineTwinPrimeSegments (by decide : 183762989 ≤ 183828525)
    (by decide : 183828525 ≤ 183894061) join_0_0 join_0_1

theorem total : (twinPrimeSegment 183762989 183894061).card = 448 := join_1_0

end S087C10
end Sude.GeneratedTwinScan
