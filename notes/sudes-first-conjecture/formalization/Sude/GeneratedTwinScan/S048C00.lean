import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S048C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 100663341 100696109 = 142 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 100663341 100696109).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 100663341 100696109
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 100696109 100728877 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 100696109 100728877).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 100696109 100728877
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 100728877 100761645 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 100728877 100761645).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 100728877 100761645
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 100761645 100794413 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 100761645 100794413).card = 110 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 100761645 100794413
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 100663341 100728877).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 100663341 ≤ 100696109)
    (by decide : 100696109 ≤ 100728877) block0 block1

theorem join_0_1 : (twinPrimeSegment 100728877 100794413).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 100728877 ≤ 100761645)
    (by decide : 100761645 ≤ 100794413) block2 block3

theorem join_1_0 : (twinPrimeSegment 100663341 100794413).card = 477 := by
  simpa using combineTwinPrimeSegments (by decide : 100663341 ≤ 100728877)
    (by decide : 100728877 ≤ 100794413) join_0_0 join_0_1

theorem total : (twinPrimeSegment 100663341 100794413).card = 477 := join_1_0

end S048C00
end Sude.GeneratedTwinScan
