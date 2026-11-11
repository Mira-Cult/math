import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S125C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16216)) 262930477 262963245 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 262930477 262963245).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16216 262930477 262963245
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16217)) 262963245 262996013 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 262963245 262996013).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16217 262963245 262996013
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16218)) 262996013 263028781 = 94 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 262996013 263028781).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16218 262996013 263028781
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16219)) 263028781 263061549 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 263028781 263061549).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16219 263028781 263061549
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 262930477 262996013).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 262930477 ≤ 262963245)
    (by decide : 262963245 ≤ 262996013) block0 block1

theorem join_0_1 : (twinPrimeSegment 262996013 263061549).card = 191 := by
  simpa using combineTwinPrimeSegments (by decide : 262996013 ≤ 263028781)
    (by decide : 263028781 ≤ 263061549) block2 block3

theorem join_1_0 : (twinPrimeSegment 262930477 263061549).card = 421 := by
  simpa using combineTwinPrimeSegments (by decide : 262930477 ≤ 262996013)
    (by decide : 262996013 ≤ 263061549) join_0_0 join_0_1

theorem total : (twinPrimeSegment 262930477 263061549).card = 421 := join_1_0

end S125C06
end Sude.GeneratedTwinScan
