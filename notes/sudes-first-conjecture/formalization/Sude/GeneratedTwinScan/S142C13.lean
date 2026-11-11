import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S142C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17307)) 299499565 299532333 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 299499565 299532333).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17307 299499565 299532333
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17307)) 299532333 299565101 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 299532333 299565101).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17307 299532333 299565101
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17308)) 299565101 299597869 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 299565101 299597869).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17308 299565101 299597869
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17309)) 299597869 299630637 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 299597869 299630637).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17309 299597869 299630637
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 299499565 299565101).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 299499565 ≤ 299532333)
    (by decide : 299532333 ≤ 299565101) block0 block1

theorem join_0_1 : (twinPrimeSegment 299565101 299630637).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 299565101 ≤ 299597869)
    (by decide : 299597869 ≤ 299630637) block2 block3

theorem join_1_0 : (twinPrimeSegment 299499565 299630637).card = 453 := by
  simpa using combineTwinPrimeSegments (by decide : 299499565 ≤ 299565101)
    (by decide : 299565101 ≤ 299630637) join_0_0 join_0_1

theorem total : (twinPrimeSegment 299499565 299630637).card = 453 := join_1_0

end S142C13
end Sude.GeneratedTwinScan
