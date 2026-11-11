import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S056C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 119013421 119046189 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 119013421 119046189).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 119013421 119046189
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 119046189 119078957 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 119046189 119078957).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 119046189 119078957
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 119078957 119111725 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 119078957 119111725).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 119078957 119111725
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 119111725 119144493 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 119111725 119144493).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 119111725 119144493
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 119013421 119078957).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 119013421 ≤ 119046189)
    (by decide : 119046189 ≤ 119078957) block0 block1

theorem join_0_1 : (twinPrimeSegment 119078957 119144493).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 119078957 ≤ 119111725)
    (by decide : 119111725 ≤ 119144493) block2 block3

theorem join_1_0 : (twinPrimeSegment 119013421 119144493).card = 487 := by
  simpa using combineTwinPrimeSegments (by decide : 119013421 ≤ 119078957)
    (by decide : 119078957 ≤ 119144493) join_0_0 join_0_1

theorem total : (twinPrimeSegment 119013421 119144493).card = 487 := join_1_0

end S056C12
end Sude.GeneratedTwinScan
