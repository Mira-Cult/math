import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S222C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21608)) 466878509 466911277 = 90 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 466878509 466911277).card = 90 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21608 466878509 466911277
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21608)) 466911277 466944045 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 466911277 466944045).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21608 466911277 466944045
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21609)) 466944045 466976813 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 466944045 466976813).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21609 466944045 466976813
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21610)) 466976813 467009581 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 466976813 467009581).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21610 466976813 467009581
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 466878509 466944045).card = 199 := by
  simpa using combineTwinPrimeSegments (by decide : 466878509 ≤ 466911277)
    (by decide : 466911277 ≤ 466944045) block0 block1

theorem join_0_1 : (twinPrimeSegment 466944045 467009581).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 466944045 ≤ 466976813)
    (by decide : 466976813 ≤ 467009581) block2 block3

theorem join_1_0 : (twinPrimeSegment 466878509 467009581).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 466878509 ≤ 466944045)
    (by decide : 466944045 ≤ 467009581) join_0_0 join_0_1

theorem total : (twinPrimeSegment 466878509 467009581).card = 442 := join_1_0

end S222C10
end Sude.GeneratedTwinScan
