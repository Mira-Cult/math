import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S171C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18972)) 359923757 359956525 = 73 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 359923757 359956525).card = 73 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18972 359923757 359956525
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18973)) 359956525 359989293 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 359956525 359989293).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18973 359956525 359989293
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18974)) 359989293 360022061 = 96 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 359989293 360022061).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18974 359989293 360022061
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18975)) 360022061 360054829 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 360022061 360054829).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18975 360022061 360054829
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 359923757 359989293).card = 180 := by
  simpa using combineTwinPrimeSegments (by decide : 359923757 ≤ 359956525)
    (by decide : 359956525 ≤ 359989293) block0 block1

theorem join_0_1 : (twinPrimeSegment 359989293 360054829).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 359989293 ≤ 360022061)
    (by decide : 360022061 ≤ 360054829) block2 block3

theorem join_1_0 : (twinPrimeSegment 359923757 360054829).card = 380 := by
  simpa using combineTwinPrimeSegments (by decide : 359923757 ≤ 359989293)
    (by decide : 359989293 ≤ 360054829) join_0_0 join_0_1

theorem total : (twinPrimeSegment 359923757 360054829).card = 380 := join_1_0

end S171C10
end Sude.GeneratedTwinScan
