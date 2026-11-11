import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S198C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20387)) 415629357 415662125 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 415629357 415662125).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20387 415629357 415662125
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20388)) 415662125 415694893 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 415662125 415694893).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20388 415662125 415694893
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20389)) 415694893 415727661 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 415694893 415727661).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20389 415694893 415727661
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20390)) 415727661 415760429 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 415727661 415760429).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20390 415727661 415760429
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 415629357 415694893).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 415629357 ≤ 415662125)
    (by decide : 415662125 ≤ 415694893) block0 block1

theorem join_0_1 : (twinPrimeSegment 415694893 415760429).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 415694893 ≤ 415727661)
    (by decide : 415727661 ≤ 415760429) block2 block3

theorem join_1_0 : (twinPrimeSegment 415629357 415760429).card = 419 := by
  simpa using combineTwinPrimeSegments (by decide : 415629357 ≤ 415694893)
    (by decide : 415694893 ≤ 415760429) join_0_0 join_0_1

theorem total : (twinPrimeSegment 415629357 415760429).card = 419 := join_1_0

end S198C03
end Sude.GeneratedTwinScan
