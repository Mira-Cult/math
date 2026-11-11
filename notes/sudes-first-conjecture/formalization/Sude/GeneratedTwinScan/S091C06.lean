import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S091C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13844)) 191627309 191660077 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 191627309 191660077).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13844 191627309 191660077
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13845)) 191660077 191692845 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 191660077 191692845).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13845 191660077 191692845
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13846)) 191692845 191725613 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 191692845 191725613).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13846 191692845 191725613
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13847)) 191725613 191758381 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 191725613 191758381).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13847 191725613 191758381
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 191627309 191692845).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 191627309 ≤ 191660077)
    (by decide : 191660077 ≤ 191692845) block0 block1

theorem join_0_1 : (twinPrimeSegment 191692845 191758381).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 191692845 ≤ 191725613)
    (by decide : 191725613 ≤ 191758381) block2 block3

theorem join_1_0 : (twinPrimeSegment 191627309 191758381).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 191627309 ≤ 191692845)
    (by decide : 191692845 ≤ 191758381) join_0_0 join_0_1

theorem total : (twinPrimeSegment 191627309 191758381).card = 468 := join_1_0

end S091C06
end Sude.GeneratedTwinScan
