import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S161C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18400)) 338559021 338591789 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 338559021 338591789).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18400 338559021 338591789
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18401)) 338591789 338624557 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 338591789 338624557).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18401 338591789 338624557
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18402)) 338624557 338657325 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 338624557 338657325).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18402 338624557 338657325
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18403)) 338657325 338690093 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 338657325 338690093).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18403 338657325 338690093
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 338559021 338624557).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 338559021 ≤ 338591789)
    (by decide : 338591789 ≤ 338624557) block0 block1

theorem join_0_1 : (twinPrimeSegment 338624557 338690093).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 338624557 ≤ 338657325)
    (by decide : 338657325 ≤ 338690093) block2 block3

theorem join_1_0 : (twinPrimeSegment 338559021 338690093).card = 470 := by
  simpa using combineTwinPrimeSegments (by decide : 338559021 ≤ 338624557)
    (by decide : 338624557 ≤ 338690093) join_0_0 join_0_1

theorem total : (twinPrimeSegment 338559021 338690093).card = 470 := join_1_0

end S161C07
end Sude.GeneratedTwinScan
