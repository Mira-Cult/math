import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S069C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 146145325 146178093 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 146145325 146178093).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 146145325 146178093
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 146178093 146210861 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 146178093 146210861).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 146178093 146210861
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 146210861 146243629 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 146210861 146243629).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 146210861 146243629
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 146243629 146276397 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 146243629 146276397).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 146243629 146276397
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 146145325 146210861).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 146145325 ≤ 146178093)
    (by decide : 146178093 ≤ 146210861) block0 block1

theorem join_0_1 : (twinPrimeSegment 146210861 146276397).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 146210861 ≤ 146243629)
    (by decide : 146243629 ≤ 146276397) block2 block3

theorem join_1_0 : (twinPrimeSegment 146145325 146276397).card = 496 := by
  simpa using combineTwinPrimeSegments (by decide : 146145325 ≤ 146210861)
    (by decide : 146210861 ≤ 146276397) join_0_0 join_0_1

theorem total : (twinPrimeSegment 146145325 146276397).card = 496 := join_1_0

end S069C11
end Sude.GeneratedTwinScan
