import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S103C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14716)) 216530989 216563757 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 216530989 216563757).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14716 216530989 216563757
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14717)) 216563757 216596525 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 216563757 216596525).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14717 216563757 216596525
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14718)) 216596525 216629293 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 216596525 216629293).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14718 216596525 216629293
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14719)) 216629293 216662061 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 216629293 216662061).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14719 216629293 216662061
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 216530989 216596525).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 216530989 ≤ 216563757)
    (by decide : 216563757 ≤ 216596525) block0 block1

theorem join_0_1 : (twinPrimeSegment 216596525 216662061).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 216596525 ≤ 216629293)
    (by decide : 216629293 ≤ 216662061) block2 block3

theorem join_1_0 : (twinPrimeSegment 216530989 216662061).card = 472 := by
  simpa using combineTwinPrimeSegments (by decide : 216530989 ≤ 216596525)
    (by decide : 216596525 ≤ 216662061) join_0_0 join_0_1

theorem total : (twinPrimeSegment 216530989 216662061).card = 472 := join_1_0

end S103C04
end Sude.GeneratedTwinScan
