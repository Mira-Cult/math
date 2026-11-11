import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S104C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14809)) 219283501 219316269 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 219283501 219316269).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14809 219283501 219316269
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14810)) 219316269 219349037 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 219316269 219349037).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14810 219316269 219349037
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14811)) 219349037 219381805 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 219349037 219381805).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14811 219349037 219381805
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14812)) 219381805 219414573 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 219381805 219414573).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14812 219381805 219414573
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 219283501 219349037).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 219283501 ≤ 219316269)
    (by decide : 219316269 ≤ 219349037) block0 block1

theorem join_0_1 : (twinPrimeSegment 219349037 219414573).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 219349037 ≤ 219381805)
    (by decide : 219381805 ≤ 219414573) block2 block3

theorem join_1_0 : (twinPrimeSegment 219283501 219414573).card = 470 := by
  simpa using combineTwinPrimeSegments (by decide : 219283501 ≤ 219349037)
    (by decide : 219349037 ≤ 219414573) join_0_0 join_0_1

theorem total : (twinPrimeSegment 219283501 219414573).card = 470 := join_1_0

end S104C09
end Sude.GeneratedTwinScan
