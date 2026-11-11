import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S239C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22400)) 501743661 501776429 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 501743661 501776429).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22400 501743661 501776429
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22401)) 501776429 501809197 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 501776429 501809197).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22401 501776429 501809197
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22401)) 501809197 501841965 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 501809197 501841965).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22401 501809197 501841965
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22402)) 501841965 501874733 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 501841965 501874733).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22402 501841965 501874733
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 501743661 501809197).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 501743661 ≤ 501776429)
    (by decide : 501776429 ≤ 501809197) block0 block1

theorem join_0_1 : (twinPrimeSegment 501809197 501874733).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 501809197 ≤ 501841965)
    (by decide : 501841965 ≤ 501874733) block2 block3

theorem join_1_0 : (twinPrimeSegment 501743661 501874733).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 501743661 ≤ 501809197)
    (by decide : 501809197 ≤ 501874733) join_0_0 join_0_1

theorem total : (twinPrimeSegment 501743661 501874733).card = 447 := join_1_0

end S239C04
end Sude.GeneratedTwinScan
