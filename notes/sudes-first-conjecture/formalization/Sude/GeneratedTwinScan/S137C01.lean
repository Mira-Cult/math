import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S137C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16955)) 287440941 287473709 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 287440941 287473709).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16955 287440941 287473709
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16956)) 287473709 287506477 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 287473709 287506477).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16956 287473709 287506477
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16956)) 287506477 287539245 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 287506477 287539245).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16956 287506477 287539245
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16957)) 287539245 287572013 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 287539245 287572013).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16957 287539245 287572013
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 287440941 287506477).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 287440941 ≤ 287473709)
    (by decide : 287473709 ≤ 287506477) block0 block1

theorem join_0_1 : (twinPrimeSegment 287506477 287572013).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 287506477 ≤ 287539245)
    (by decide : 287539245 ≤ 287572013) block2 block3

theorem join_1_0 : (twinPrimeSegment 287440941 287572013).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 287440941 ≤ 287506477)
    (by decide : 287506477 ≤ 287572013) join_0_0 join_0_1

theorem total : (twinPrimeSegment 287440941 287572013).card = 457 := join_1_0

end S137C01
end Sude.GeneratedTwinScan
