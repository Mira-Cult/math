import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S233C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22129)) 489685037 489717805 = 97 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 489685037 489717805).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22129 489685037 489717805
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22130)) 489717805 489750573 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 489717805 489750573).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22130 489717805 489750573
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22131)) 489750573 489783341 = 91 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 489750573 489783341).card = 91 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22131 489750573 489783341
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22131)) 489783341 489816109 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 489783341 489816109).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22131 489783341 489816109
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 489685037 489750573).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 489685037 ≤ 489717805)
    (by decide : 489717805 ≤ 489750573) block0 block1

theorem join_0_1 : (twinPrimeSegment 489750573 489816109).card = 192 := by
  simpa using combineTwinPrimeSegments (by decide : 489750573 ≤ 489783341)
    (by decide : 489783341 ≤ 489816109) block2 block3

theorem join_1_0 : (twinPrimeSegment 489685037 489816109).card = 402 := by
  simpa using combineTwinPrimeSegments (by decide : 489685037 ≤ 489750573)
    (by decide : 489750573 ≤ 489816109) join_0_0 join_0_1

theorem total : (twinPrimeSegment 489685037 489816109).card = 402 := join_1_0

end S233C08
end Sude.GeneratedTwinScan
