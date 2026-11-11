import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S134C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16807)) 282460205 282492973 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 282460205 282492973).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16807 282460205 282492973
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16808)) 282492973 282525741 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 282492973 282525741).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16808 282492973 282525741
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16809)) 282525741 282558509 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 282525741 282558509).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16809 282525741 282558509
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16810)) 282558509 282591277 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 282558509 282591277).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16810 282558509 282591277
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 282460205 282525741).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 282460205 ≤ 282492973)
    (by decide : 282492973 ≤ 282525741) block0 block1

theorem join_0_1 : (twinPrimeSegment 282525741 282591277).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 282525741 ≤ 282558509)
    (by decide : 282558509 ≤ 282591277) block2 block3

theorem join_1_0 : (twinPrimeSegment 282460205 282591277).card = 478 := by
  simpa using combineTwinPrimeSegments (by decide : 282460205 ≤ 282525741)
    (by decide : 282525741 ≤ 282591277) join_0_0 join_0_1

theorem total : (twinPrimeSegment 282460205 282591277).card = 478 := join_1_0

end S134C11
end Sude.GeneratedTwinScan
