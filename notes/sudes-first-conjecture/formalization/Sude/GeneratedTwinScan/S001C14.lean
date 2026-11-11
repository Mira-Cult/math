import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S001C13

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S001C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 3932205 widths0 = 195 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 3932205 3964973).card = 195 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 3932205 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 3932205 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 3932205 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 3964973 widths1 = 169 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 3964973 3997741).card = 169 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 3964973 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 3964973 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 3964973 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 3997741 widths2 = 197 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 3997741 4030509).card = 197 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 3997741 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 3997741 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 3997741 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 4030509 widths3 = 213 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 4030509 4063277).card = 213 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 4030509 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 4030509 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 4030509 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 3932205 3997741).card = 364 := by
  simpa using combineTwinPrimeSegments (by decide : 3932205 ≤ 3964973)
    (by decide : 3964973 ≤ 3997741) block0 block1

theorem join_0_1 : (twinPrimeSegment 3997741 4063277).card = 410 := by
  simpa using combineTwinPrimeSegments (by decide : 3997741 ≤ 4030509)
    (by decide : 4030509 ≤ 4063277) block2 block3

theorem join_1_0 : (twinPrimeSegment 3932205 4063277).card = 774 := by
  simpa using combineTwinPrimeSegments (by decide : 3932205 ≤ 3997741)
    (by decide : 3997741 ≤ 4063277) join_0_0 join_0_1

theorem total : (twinPrimeSegment 3932205 4063277).card = 774 := join_1_0

end S001C14
end Sude.GeneratedTwinScan
