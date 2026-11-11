import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S071C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 150339629 150372397 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 150339629 150372397).card = 100 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 150339629 150372397
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 150372397 150405165 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 150372397 150405165).card = 108 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 150372397 150405165
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 150405165 150437933 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 150405165 150437933).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 150405165 150437933
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 150437933 150470701 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 150437933 150470701).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 150437933 150470701
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 150339629 150405165).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 150339629 ≤ 150372397)
    (by decide : 150372397 ≤ 150405165) block0 block1

theorem join_0_1 : (twinPrimeSegment 150405165 150470701).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 150405165 ≤ 150437933)
    (by decide : 150437933 ≤ 150470701) block2 block3

theorem join_1_0 : (twinPrimeSegment 150339629 150470701).card = 459 := by
  simpa using combineTwinPrimeSegments (by decide : 150339629 ≤ 150405165)
    (by decide : 150405165 ≤ 150470701) join_0_0 join_0_1

theorem total : (twinPrimeSegment 150339629 150470701).card = 459 := join_1_0

end S071C11
end Sude.GeneratedTwinScan
