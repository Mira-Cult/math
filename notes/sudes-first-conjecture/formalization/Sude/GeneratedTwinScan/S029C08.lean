import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S029C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 61866029 61898797 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 61866029 61898797).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 61866029 61898797
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 61898797 61931565 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 61898797 61931565).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 61898797 61931565
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 61931565 61964333 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 61931565 61964333).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 61931565 61964333
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 61964333 61997101 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 61964333 61997101).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 61964333 61997101
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 61866029 61931565).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 61866029 ≤ 61898797)
    (by decide : 61898797 ≤ 61931565) block0 block1

theorem join_0_1 : (twinPrimeSegment 61931565 61997101).card = 267 := by
  simpa using combineTwinPrimeSegments (by decide : 61931565 ≤ 61964333)
    (by decide : 61964333 ≤ 61997101) block2 block3

theorem join_1_0 : (twinPrimeSegment 61866029 61997101).card = 516 := by
  simpa using combineTwinPrimeSegments (by decide : 61866029 ≤ 61931565)
    (by decide : 61931565 ≤ 61997101) join_0_0 join_0_1

theorem total : (twinPrimeSegment 61866029 61997101).card = 516 := join_1_0

end S029C08
end Sude.GeneratedTwinScan
