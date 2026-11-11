import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S230C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21995)) 483786797 483819565 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 483786797 483819565).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21995 483786797 483819565
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21996)) 483819565 483852333 = 90 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 483819565 483852333).card = 90 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21996 483819565 483852333
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21997)) 483852333 483885101 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 483852333 483885101).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21997 483852333 483885101
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21998)) 483885101 483917869 = 88 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 483885101 483917869).card = 88 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21998 483885101 483917869
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 483786797 483852333).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 483786797 ≤ 483819565)
    (by decide : 483819565 ≤ 483852333) block0 block1

theorem join_0_1 : (twinPrimeSegment 483852333 483917869).card = 197 := by
  simpa using combineTwinPrimeSegments (by decide : 483852333 ≤ 483885101)
    (by decide : 483885101 ≤ 483917869) block2 block3

theorem join_1_0 : (twinPrimeSegment 483786797 483917869).card = 401 := by
  simpa using combineTwinPrimeSegments (by decide : 483786797 ≤ 483852333)
    (by decide : 483852333 ≤ 483917869) join_0_0 join_0_1

theorem total : (twinPrimeSegment 483786797 483917869).card = 401 := join_1_0

end S230C11
end Sude.GeneratedTwinScan
