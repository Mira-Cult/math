import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S076C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12646)) 159907885 159940653 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 159907885 159940653).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12646 159907885 159940653
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12648)) 159940653 159973421 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 159940653 159973421).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12648 159940653 159973421
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12649)) 159973421 160006189 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 159973421 160006189).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12649 159973421 160006189
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12650)) 160006189 160038957 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 160006189 160038957).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12650 160006189 160038957
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 159907885 159973421).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 159907885 ≤ 159940653)
    (by decide : 159940653 ≤ 159973421) block0 block1

theorem join_0_1 : (twinPrimeSegment 159973421 160038957).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 159973421 ≤ 160006189)
    (by decide : 160006189 ≤ 160038957) block2 block3

theorem join_1_0 : (twinPrimeSegment 159907885 160038957).card = 479 := by
  simpa using combineTwinPrimeSegments (by decide : 159907885 ≤ 159973421)
    (by decide : 159973421 ≤ 160038957) join_0_0 join_0_1

theorem total : (twinPrimeSegment 159907885 160038957).card = 479 := join_1_0

end S076C04
end Sude.GeneratedTwinScan
