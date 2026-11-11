import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S152C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17858)) 318898221 318930989 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 318898221 318930989).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17858 318898221 318930989
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17859)) 318930989 318963757 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 318930989 318963757).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17859 318930989 318963757
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17860)) 318963757 318996525 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 318963757 318996525).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17860 318963757 318996525
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17861)) 318996525 319029293 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 318996525 319029293).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17861 318996525 319029293
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 318898221 318963757).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 318898221 ≤ 318930989)
    (by decide : 318930989 ≤ 318963757) block0 block1

theorem join_0_1 : (twinPrimeSegment 318963757 319029293).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 318963757 ≤ 318996525)
    (by decide : 318996525 ≤ 319029293) block2 block3

theorem join_1_0 : (twinPrimeSegment 318898221 319029293).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 318898221 ≤ 318963757)
    (by decide : 318963757 ≤ 319029293) join_0_0 join_0_1

theorem total : (twinPrimeSegment 318898221 319029293).card = 443 := join_1_0

end S152C01
end Sude.GeneratedTwinScan
