import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S185C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19737)) 389546029 389578797 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 389546029 389578797).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19737 389546029 389578797
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19738)) 389578797 389611565 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 389578797 389611565).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19738 389578797 389611565
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19739)) 389611565 389644333 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 389611565 389644333).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19739 389611565 389644333
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19740)) 389644333 389677101 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 389644333 389677101).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19740 389644333 389677101
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 389546029 389611565).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 389546029 ≤ 389578797)
    (by decide : 389578797 ≤ 389611565) block0 block1

theorem join_0_1 : (twinPrimeSegment 389611565 389677101).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 389611565 ≤ 389644333)
    (by decide : 389644333 ≤ 389677101) block2 block3

theorem join_1_0 : (twinPrimeSegment 389546029 389677101).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 389546029 ≤ 389611565)
    (by decide : 389611565 ≤ 389677101) join_0_0 join_0_1

theorem total : (twinPrimeSegment 389546029 389677101).card = 441 := join_1_0

end S185C12
end Sude.GeneratedTwinScan
