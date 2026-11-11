import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S189C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19945)) 397803565 397836333 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 397803565 397836333).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19945 397803565 397836333
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19946)) 397836333 397869101 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 397836333 397869101).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19946 397836333 397869101
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19947)) 397869101 397901869 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 397869101 397901869).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19947 397869101 397901869
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19948)) 397901869 397934637 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 397901869 397934637).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19948 397901869 397934637
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 397803565 397869101).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 397803565 ≤ 397836333)
    (by decide : 397836333 ≤ 397869101) block0 block1

theorem join_0_1 : (twinPrimeSegment 397869101 397934637).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 397869101 ≤ 397901869)
    (by decide : 397901869 ≤ 397934637) block2 block3

theorem join_1_0 : (twinPrimeSegment 397803565 397934637).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 397803565 ≤ 397869101)
    (by decide : 397869101 ≤ 397934637) join_0_0 join_0_1

theorem total : (twinPrimeSegment 397803565 397934637).card = 468 := join_1_0

end S189C11
end Sude.GeneratedTwinScan
