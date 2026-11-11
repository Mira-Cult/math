import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S084C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13298)) 176816173 176848941 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 176816173 176848941).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13298 176816173 176848941
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13299)) 176848941 176881709 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 176848941 176881709).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13299 176848941 176881709
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13300)) 176881709 176914477 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 176881709 176914477).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13300 176881709 176914477
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13302)) 176914477 176947245 = 139 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 176914477 176947245).card = 139 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13302 176914477 176947245
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 176816173 176881709).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 176816173 ≤ 176848941)
    (by decide : 176848941 ≤ 176881709) block0 block1

theorem join_0_1 : (twinPrimeSegment 176881709 176947245).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 176881709 ≤ 176914477)
    (by decide : 176914477 ≤ 176947245) block2 block3

theorem join_1_0 : (twinPrimeSegment 176816173 176947245).card = 474 := by
  simpa using combineTwinPrimeSegments (by decide : 176816173 ≤ 176881709)
    (by decide : 176881709 ≤ 176947245) join_0_0 join_0_1

theorem total : (twinPrimeSegment 176816173 176947245).card = 474 := join_1_0

end S084C05
end Sude.GeneratedTwinScan
