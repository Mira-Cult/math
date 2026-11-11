import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S181C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19483)) 379584557 379617325 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 379584557 379617325).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19483 379584557 379617325
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19484)) 379617325 379650093 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 379617325 379650093).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19484 379617325 379650093
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19485)) 379650093 379682861 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 379650093 379682861).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19485 379650093 379682861
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19486)) 379682861 379715629 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 379682861 379715629).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19486 379682861 379715629
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 379584557 379650093).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 379584557 ≤ 379617325)
    (by decide : 379617325 ≤ 379650093) block0 block1

theorem join_0_1 : (twinPrimeSegment 379650093 379715629).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 379650093 ≤ 379682861)
    (by decide : 379682861 ≤ 379715629) block2 block3

theorem join_1_0 : (twinPrimeSegment 379584557 379715629).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 379584557 ≤ 379650093)
    (by decide : 379650093 ≤ 379715629) join_0_0 join_0_1

theorem total : (twinPrimeSegment 379584557 379715629).card = 462 := join_1_0

end S181C00
end Sude.GeneratedTwinScan
