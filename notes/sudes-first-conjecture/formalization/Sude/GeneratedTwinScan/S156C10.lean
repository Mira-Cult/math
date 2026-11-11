import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S156C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18124)) 328466477 328499245 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 328466477 328499245).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18124 328466477 328499245
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18125)) 328499245 328532013 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 328499245 328532013).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18125 328499245 328532013
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18126)) 328532013 328564781 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 328532013 328564781).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18126 328532013 328564781
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18127)) 328564781 328597549 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 328564781 328597549).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18127 328564781 328597549
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 328466477 328532013).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 328466477 ≤ 328499245)
    (by decide : 328499245 ≤ 328532013) block0 block1

theorem join_0_1 : (twinPrimeSegment 328532013 328597549).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 328532013 ≤ 328564781)
    (by decide : 328564781 ≤ 328597549) block2 block3

theorem join_1_0 : (twinPrimeSegment 328466477 328597549).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 328466477 ≤ 328532013)
    (by decide : 328532013 ≤ 328597549) join_0_0 join_0_1

theorem total : (twinPrimeSegment 328466477 328597549).card = 444 := join_1_0

end S156C10
end Sude.GeneratedTwinScan
