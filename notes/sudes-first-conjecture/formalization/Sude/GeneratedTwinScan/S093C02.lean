import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S093C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13976)) 195297325 195330093 = 95 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 195297325 195330093).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13976 195297325 195330093
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13977)) 195330093 195362861 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 195330093 195362861).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13977 195330093 195362861
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13978)) 195362861 195395629 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 195362861 195395629).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13978 195362861 195395629
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13979)) 195395629 195428397 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 195395629 195428397).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13979 195395629 195428397
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 195297325 195362861).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 195297325 ≤ 195330093)
    (by decide : 195330093 ≤ 195362861) block0 block1

theorem join_0_1 : (twinPrimeSegment 195362861 195428397).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 195362861 ≤ 195395629)
    (by decide : 195395629 ≤ 195428397) block2 block3

theorem join_1_0 : (twinPrimeSegment 195297325 195428397).card = 448 := by
  simpa using combineTwinPrimeSegments (by decide : 195297325 ≤ 195362861)
    (by decide : 195362861 ≤ 195428397) join_0_0 join_0_1

theorem total : (twinPrimeSegment 195297325 195428397).card = 448 := join_1_0

end S093C02
end Sude.GeneratedTwinScan
