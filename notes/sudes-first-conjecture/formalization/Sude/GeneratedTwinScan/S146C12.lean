import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S146C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17543)) 307757101 307789869 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 307757101 307789869).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17543 307757101 307789869
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17544)) 307789869 307822637 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 307789869 307822637).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17544 307789869 307822637
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17545)) 307822637 307855405 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 307822637 307855405).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17545 307822637 307855405
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17546)) 307855405 307888173 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 307855405 307888173).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17546 307855405 307888173
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 307757101 307822637).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 307757101 ≤ 307789869)
    (by decide : 307789869 ≤ 307822637) block0 block1

theorem join_0_1 : (twinPrimeSegment 307822637 307888173).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 307822637 ≤ 307855405)
    (by decide : 307855405 ≤ 307888173) block2 block3

theorem join_1_0 : (twinPrimeSegment 307757101 307888173).card = 475 := by
  simpa using combineTwinPrimeSegments (by decide : 307757101 ≤ 307822637)
    (by decide : 307822637 ≤ 307888173) join_0_0 join_0_1

theorem total : (twinPrimeSegment 307757101 307888173).card = 475 := join_1_0

end S146C12
end Sude.GeneratedTwinScan
