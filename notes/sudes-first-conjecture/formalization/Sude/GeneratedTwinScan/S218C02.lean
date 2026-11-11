import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S218C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21388)) 457441325 457474093 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 457441325 457474093).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21388 457441325 457474093
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21389)) 457474093 457506861 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 457474093 457506861).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21389 457474093 457506861
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21390)) 457506861 457539629 = 90 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 457506861 457539629).card = 90 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21390 457506861 457539629
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21390)) 457539629 457572397 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 457539629 457572397).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21390 457539629 457572397
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 457441325 457506861).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 457441325 ≤ 457474093)
    (by decide : 457474093 ≤ 457506861) block0 block1

theorem join_0_1 : (twinPrimeSegment 457506861 457572397).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 457506861 ≤ 457539629)
    (by decide : 457539629 ≤ 457572397) block2 block3

theorem join_1_0 : (twinPrimeSegment 457441325 457572397).card = 421 := by
  simpa using combineTwinPrimeSegments (by decide : 457441325 ≤ 457506861)
    (by decide : 457506861 ≤ 457572397) join_0_0 join_0_1

theorem total : (twinPrimeSegment 457441325 457572397).card = 421 := join_1_0

end S218C02
end Sude.GeneratedTwinScan
