import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S239C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22414)) 502399021 502431789 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 502399021 502431789).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22414 502399021 502431789
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22415)) 502431789 502464557 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 502431789 502464557).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22415 502431789 502464557
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22416)) 502464557 502497325 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 502464557 502497325).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22416 502464557 502497325
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22417)) 502497325 502530093 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 502497325 502530093).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22417 502497325 502530093
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 502399021 502464557).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 502399021 ≤ 502431789)
    (by decide : 502431789 ≤ 502464557) block0 block1

theorem join_0_1 : (twinPrimeSegment 502464557 502530093).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 502464557 ≤ 502497325)
    (by decide : 502497325 ≤ 502530093) block2 block3

theorem join_1_0 : (twinPrimeSegment 502399021 502530093).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 502399021 ≤ 502464557)
    (by decide : 502464557 ≤ 502530093) join_0_0 join_0_1

theorem total : (twinPrimeSegment 502399021 502530093).card = 440 := join_1_0

end S239C09
end Sude.GeneratedTwinScan
