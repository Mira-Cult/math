import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S151C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17821)) 317587501 317620269 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 317587501 317620269).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17821 317587501 317620269
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17822)) 317620269 317653037 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 317620269 317653037).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17822 317620269 317653037
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17823)) 317653037 317685805 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 317653037 317685805).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17823 317653037 317685805
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17824)) 317685805 317718573 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 317685805 317718573).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17824 317685805 317718573
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 317587501 317653037).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 317587501 ≤ 317620269)
    (by decide : 317620269 ≤ 317653037) block0 block1

theorem join_0_1 : (twinPrimeSegment 317653037 317718573).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 317653037 ≤ 317685805)
    (by decide : 317685805 ≤ 317718573) block2 block3

theorem join_1_0 : (twinPrimeSegment 317587501 317718573).card = 474 := by
  simpa using combineTwinPrimeSegments (by decide : 317587501 ≤ 317653037)
    (by decide : 317653037 ≤ 317718573) join_0_0 join_0_1

theorem total : (twinPrimeSegment 317587501 317718573).card = 474 := join_1_0

end S151C07
end Sude.GeneratedTwinScan
