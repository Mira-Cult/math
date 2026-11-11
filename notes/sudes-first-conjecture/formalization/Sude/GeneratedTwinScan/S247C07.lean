import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S247C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22780)) 518914093 518946861 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 518914093 518946861).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22780 518914093 518946861
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22781)) 518946861 518979629 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 518946861 518979629).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22781 518946861 518979629
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22781)) 518979629 519012397 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 518979629 519012397).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22781 518979629 519012397
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22782)) 519012397 519045165 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 519012397 519045165).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22782 519012397 519045165
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 518914093 518979629).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 518914093 ≤ 518946861)
    (by decide : 518946861 ≤ 518979629) block0 block1

theorem join_0_1 : (twinPrimeSegment 518979629 519045165).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 518979629 ≤ 519012397)
    (by decide : 519012397 ≤ 519045165) block2 block3

theorem join_1_0 : (twinPrimeSegment 518914093 519045165).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 518914093 ≤ 518979629)
    (by decide : 518979629 ≤ 519045165) join_0_0 join_0_1

theorem total : (twinPrimeSegment 518914093 519045165).card = 440 := join_1_0

end S247C07
end Sude.GeneratedTwinScan
