import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S121C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15930)) 253755437 253788205 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 253755437 253788205).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15930 253755437 253788205
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15931)) 253788205 253820973 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 253788205 253820973).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15931 253788205 253820973
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15932)) 253820973 253853741 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 253820973 253853741).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15932 253820973 253853741
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15933)) 253853741 253886509 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 253853741 253886509).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15933 253853741 253886509
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 253755437 253820973).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 253755437 ≤ 253788205)
    (by decide : 253788205 ≤ 253820973) block0 block1

theorem join_0_1 : (twinPrimeSegment 253820973 253886509).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 253820973 ≤ 253853741)
    (by decide : 253853741 ≤ 253886509) block2 block3

theorem join_1_0 : (twinPrimeSegment 253755437 253886509).card = 481 := by
  simpa using combineTwinPrimeSegments (by decide : 253755437 ≤ 253820973)
    (by decide : 253820973 ≤ 253886509) join_0_0 join_0_1

theorem total : (twinPrimeSegment 253755437 253886509).card = 481 := join_1_0

end S121C00
end Sude.GeneratedTwinScan
