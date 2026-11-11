import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S000C00

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S000C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 131117 widths0 = 309 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 131117 163885).card = 309 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 131117 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 131117 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 131117 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 163885 widths1 = 291 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 163885 196653).card = 291 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 163885 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 163885 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 163885 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 196653 widths2 = 286 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 196653 229421).card = 286 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 196653 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 196653 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 196653 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 229421 widths3 = 267 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 229421 262189).card = 267 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 229421 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 229421 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 229421 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 131117 196653).card = 600 := by
  simpa using combineTwinPrimeSegments (by decide : 131117 ≤ 163885)
    (by decide : 163885 ≤ 196653) block0 block1

theorem join_0_1 : (twinPrimeSegment 196653 262189).card = 553 := by
  simpa using combineTwinPrimeSegments (by decide : 196653 ≤ 229421)
    (by decide : 229421 ≤ 262189) block2 block3

theorem join_1_0 : (twinPrimeSegment 131117 262189).card = 1153 := by
  simpa using combineTwinPrimeSegments (by decide : 131117 ≤ 196653)
    (by decide : 196653 ≤ 262189) join_0_0 join_0_1

theorem total : (twinPrimeSegment 131117 262189).card = 1153 := join_1_0

end S000C01
end Sude.GeneratedTwinScan
