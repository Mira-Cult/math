import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S116C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15652)) 244973613 245006381 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 244973613 245006381).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15652 244973613 245006381
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15653)) 245006381 245039149 = 95 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 245006381 245039149).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15653 245006381 245039149
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15654)) 245039149 245071917 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 245039149 245071917).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15654 245039149 245071917
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15655)) 245071917 245104685 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 245071917 245104685).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15655 245071917 245104685
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 244973613 245039149).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 244973613 ≤ 245006381)
    (by decide : 245006381 ≤ 245039149) block0 block1

theorem join_0_1 : (twinPrimeSegment 245039149 245104685).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 245039149 ≤ 245071917)
    (by decide : 245071917 ≤ 245104685) block2 block3

theorem join_1_0 : (twinPrimeSegment 244973613 245104685).card = 422 := by
  simpa using combineTwinPrimeSegments (by decide : 244973613 ≤ 245039149)
    (by decide : 245039149 ≤ 245104685) join_0_0 join_0_1

theorem total : (twinPrimeSegment 244973613 245104685).card = 422 := join_1_0

end S116C13
end Sude.GeneratedTwinScan
