import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S178C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19325)) 373424173 373456941 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 373424173 373456941).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19325 373424173 373456941
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19325)) 373456941 373489709 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 373456941 373489709).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19325 373456941 373489709
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19326)) 373489709 373522477 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 373489709 373522477).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19326 373489709 373522477
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19327)) 373522477 373555245 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 373522477 373555245).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19327 373522477 373555245
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 373424173 373489709).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 373424173 ≤ 373456941)
    (by decide : 373456941 ≤ 373489709) block0 block1

theorem join_0_1 : (twinPrimeSegment 373489709 373555245).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 373489709 ≤ 373522477)
    (by decide : 373522477 ≤ 373555245) block2 block3

theorem join_1_0 : (twinPrimeSegment 373424173 373555245).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 373424173 ≤ 373489709)
    (by decide : 373489709 ≤ 373555245) join_0_0 join_0_1

theorem total : (twinPrimeSegment 373424173 373555245).card = 449 := join_1_0

end S178C01
end Sude.GeneratedTwinScan
