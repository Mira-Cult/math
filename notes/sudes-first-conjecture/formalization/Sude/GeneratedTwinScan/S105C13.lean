import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S105C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14897)) 221904941 221937709 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 221904941 221937709).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14897 221904941 221937709
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14898)) 221937709 221970477 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 221937709 221970477).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14898 221937709 221970477
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14899)) 221970477 222003245 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 221970477 222003245).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14899 221970477 222003245
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14900)) 222003245 222036013 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 222003245 222036013).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14900 222003245 222036013
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 221904941 221970477).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 221904941 ≤ 221937709)
    (by decide : 221937709 ≤ 221970477) block0 block1

theorem join_0_1 : (twinPrimeSegment 221970477 222036013).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 221970477 ≤ 222003245)
    (by decide : 222003245 ≤ 222036013) block2 block3

theorem join_1_0 : (twinPrimeSegment 221904941 222036013).card = 481 := by
  simpa using combineTwinPrimeSegments (by decide : 221904941 ≤ 221970477)
    (by decide : 221970477 ≤ 222036013) join_0_0 join_0_1

theorem total : (twinPrimeSegment 221904941 222036013).card = 481 := join_1_0

end S105C13
end Sude.GeneratedTwinScan
