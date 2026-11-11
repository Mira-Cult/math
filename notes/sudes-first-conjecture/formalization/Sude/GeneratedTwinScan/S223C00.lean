import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S223C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21626)) 467664941 467697709 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 467664941 467697709).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21626 467664941 467697709
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21627)) 467697709 467730477 = 84 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 467697709 467730477).card = 84 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21627 467697709 467730477
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21627)) 467730477 467763245 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 467730477 467763245).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21627 467730477 467763245
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21628)) 467763245 467796013 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 467763245 467796013).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21628 467763245 467796013
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 467664941 467730477).card = 189 := by
  simpa using combineTwinPrimeSegments (by decide : 467664941 ≤ 467697709)
    (by decide : 467697709 ≤ 467730477) block0 block1

theorem join_0_1 : (twinPrimeSegment 467730477 467796013).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 467730477 ≤ 467763245)
    (by decide : 467763245 ≤ 467796013) block2 block3

theorem join_1_0 : (twinPrimeSegment 467664941 467796013).card = 420 := by
  simpa using combineTwinPrimeSegments (by decide : 467664941 ≤ 467730477)
    (by decide : 467730477 ≤ 467796013) join_0_0 join_0_1

theorem total : (twinPrimeSegment 467664941 467796013).card = 420 := join_1_0

end S223C00
end Sude.GeneratedTwinScan
