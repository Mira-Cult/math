import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S157C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18149)) 329383981 329416749 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 329383981 329416749).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18149 329383981 329416749
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18150)) 329416749 329449517 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 329416749 329449517).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18150 329416749 329449517
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18151)) 329449517 329482285 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 329449517 329482285).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18151 329449517 329482285
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18152)) 329482285 329515053 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 329482285 329515053).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18152 329482285 329515053
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 329383981 329449517).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 329383981 ≤ 329416749)
    (by decide : 329416749 ≤ 329449517) block0 block1

theorem join_0_1 : (twinPrimeSegment 329449517 329515053).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 329449517 ≤ 329482285)
    (by decide : 329482285 ≤ 329515053) block2 block3

theorem join_1_0 : (twinPrimeSegment 329383981 329515053).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 329383981 ≤ 329449517)
    (by decide : 329449517 ≤ 329515053) join_0_0 join_0_1

theorem total : (twinPrimeSegment 329383981 329515053).card = 482 := join_1_0

end S157C01
end Sude.GeneratedTwinScan
