import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S143C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17371)) 301727789 301760557 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 301727789 301760557).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17371 301727789 301760557
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17372)) 301760557 301793325 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 301760557 301793325).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17372 301760557 301793325
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17373)) 301793325 301826093 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 301793325 301826093).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17373 301793325 301826093
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17374)) 301826093 301858861 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 301826093 301858861).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17374 301826093 301858861
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 301727789 301793325).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 301727789 ≤ 301760557)
    (by decide : 301760557 ≤ 301793325) block0 block1

theorem join_0_1 : (twinPrimeSegment 301793325 301858861).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 301793325 ≤ 301826093)
    (by decide : 301826093 ≤ 301858861) block2 block3

theorem join_1_0 : (twinPrimeSegment 301727789 301858861).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 301727789 ≤ 301793325)
    (by decide : 301793325 ≤ 301858861) join_0_0 join_0_1

theorem total : (twinPrimeSegment 301727789 301858861).card = 444 := join_1_0

end S143C14
end Sude.GeneratedTwinScan
