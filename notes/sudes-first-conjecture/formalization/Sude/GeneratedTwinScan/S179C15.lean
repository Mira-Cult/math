import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S179C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19426)) 377356333 377389101 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 377356333 377389101).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19426 377356333 377389101
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19427)) 377389101 377421869 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 377389101 377421869).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19427 377389101 377421869
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19428)) 377421869 377454637 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 377421869 377454637).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19428 377421869 377454637
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19429)) 377454637 377487405 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 377454637 377487405).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19429 377454637 377487405
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 377356333 377421869).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 377356333 ≤ 377389101)
    (by decide : 377389101 ≤ 377421869) block0 block1

theorem join_0_1 : (twinPrimeSegment 377421869 377487405).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 377421869 ≤ 377454637)
    (by decide : 377454637 ≤ 377487405) block2 block3

theorem join_1_0 : (twinPrimeSegment 377356333 377487405).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 377356333 ≤ 377421869)
    (by decide : 377421869 ≤ 377487405) join_0_0 join_0_1

theorem total : (twinPrimeSegment 377356333 377487405).card = 438 := join_1_0

end S179C15
end Sude.GeneratedTwinScan
