import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S197C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20368)) 414842925 414875693 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 414842925 414875693).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20368 414842925 414875693
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20369)) 414875693 414908461 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 414875693 414908461).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20369 414875693 414908461
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20370)) 414908461 414941229 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 414908461 414941229).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20370 414908461 414941229
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20370)) 414941229 414973997 = 89 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 414941229 414973997).card = 89 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20370 414941229 414973997
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 414842925 414908461).card = 199 := by
  simpa using combineTwinPrimeSegments (by decide : 414842925 ≤ 414875693)
    (by decide : 414875693 ≤ 414908461) block0 block1

theorem join_0_1 : (twinPrimeSegment 414908461 414973997).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 414908461 ≤ 414941229)
    (by decide : 414941229 ≤ 414973997) block2 block3

theorem join_1_0 : (twinPrimeSegment 414842925 414973997).card = 401 := by
  simpa using combineTwinPrimeSegments (by decide : 414842925 ≤ 414908461)
    (by decide : 414908461 ≤ 414973997) join_0_0 join_0_1

theorem total : (twinPrimeSegment 414842925 414973997).card = 401 := join_1_0

end S197C13
end Sude.GeneratedTwinScan
