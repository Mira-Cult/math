import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S135C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16854)) 284033069 284065837 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 284033069 284065837).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16854 284033069 284065837
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16855)) 284065837 284098605 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 284065837 284098605).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16855 284065837 284098605
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16856)) 284098605 284131373 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 284098605 284131373).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16856 284098605 284131373
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16857)) 284131373 284164141 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 284131373 284164141).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16857 284131373 284164141
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 284033069 284098605).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 284033069 ≤ 284065837)
    (by decide : 284065837 ≤ 284098605) block0 block1

theorem join_0_1 : (twinPrimeSegment 284098605 284164141).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 284098605 ≤ 284131373)
    (by decide : 284131373 ≤ 284164141) block2 block3

theorem join_1_0 : (twinPrimeSegment 284033069 284164141).card = 459 := by
  simpa using combineTwinPrimeSegments (by decide : 284033069 ≤ 284098605)
    (by decide : 284098605 ≤ 284164141) join_0_0 join_0_1

theorem total : (twinPrimeSegment 284033069 284164141).card = 459 := join_1_0

end S135C07
end Sude.GeneratedTwinScan
