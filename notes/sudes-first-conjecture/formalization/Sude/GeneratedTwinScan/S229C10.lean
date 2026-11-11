import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S229C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21945)) 481558573 481591341 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 481558573 481591341).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21945 481558573 481591341
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21945)) 481591341 481624109 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 481591341 481624109).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21945 481591341 481624109
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21946)) 481624109 481656877 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 481624109 481656877).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21946 481624109 481656877
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21947)) 481656877 481689645 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 481656877 481689645).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21947 481656877 481689645
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 481558573 481624109).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 481558573 ≤ 481591341)
    (by decide : 481591341 ≤ 481624109) block0 block1

theorem join_0_1 : (twinPrimeSegment 481624109 481689645).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 481624109 ≤ 481656877)
    (by decide : 481656877 ≤ 481689645) block2 block3

theorem join_1_0 : (twinPrimeSegment 481558573 481689645).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 481558573 ≤ 481624109)
    (by decide : 481624109 ≤ 481689645) join_0_0 join_0_1

theorem total : (twinPrimeSegment 481558573 481689645).card = 426 := join_1_0

end S229C10
end Sude.GeneratedTwinScan
