import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S004C08

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S004C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 9568301 widths0 = 167 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 9568301 9601069).card = 167 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 9568301 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 9568301 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 9568301 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 9601069 widths1 = 169 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 9601069 9633837).card = 169 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 9601069 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 9601069 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 9601069 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 9633837 widths2 = 174 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 9633837 9666605).card = 174 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 9633837 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 9633837 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 9633837 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 9666605 widths3 = 167 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 9666605 9699373).card = 167 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 9666605 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 9666605 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 9666605 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 9568301 9633837).card = 336 := by
  simpa using combineTwinPrimeSegments (by decide : 9568301 ≤ 9601069)
    (by decide : 9601069 ≤ 9633837) block0 block1

theorem join_0_1 : (twinPrimeSegment 9633837 9699373).card = 341 := by
  simpa using combineTwinPrimeSegments (by decide : 9633837 ≤ 9666605)
    (by decide : 9666605 ≤ 9699373) block2 block3

theorem join_1_0 : (twinPrimeSegment 9568301 9699373).card = 677 := by
  simpa using combineTwinPrimeSegments (by decide : 9568301 ≤ 9633837)
    (by decide : 9633837 ≤ 9699373) join_0_0 join_0_1

theorem total : (twinPrimeSegment 9568301 9699373).card = 677 := join_1_0

end S004C09
end Sude.GeneratedTwinScan
