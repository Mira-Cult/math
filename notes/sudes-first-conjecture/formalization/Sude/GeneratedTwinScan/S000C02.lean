import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S000C01

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S000C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 262189 widths0 = 274 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 262189 294957).card = 274 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 262189 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 262189 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 262189 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 294957 widths1 = 296 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 294957 327725).card = 296 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 294957 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 294957 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 294957 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 327725 widths2 = 255 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 327725 360493).card = 255 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 327725 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 327725 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 327725 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 360493 widths3 = 246 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 360493 393261).card = 246 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 360493 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 360493 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 360493 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 262189 327725).card = 570 := by
  simpa using combineTwinPrimeSegments (by decide : 262189 ≤ 294957)
    (by decide : 294957 ≤ 327725) block0 block1

theorem join_0_1 : (twinPrimeSegment 327725 393261).card = 501 := by
  simpa using combineTwinPrimeSegments (by decide : 327725 ≤ 360493)
    (by decide : 360493 ≤ 393261) block2 block3

theorem join_1_0 : (twinPrimeSegment 262189 393261).card = 1071 := by
  simpa using combineTwinPrimeSegments (by decide : 262189 ≤ 327725)
    (by decide : 327725 ≤ 393261) join_0_0 join_0_1

theorem total : (twinPrimeSegment 262189 393261).card = 1071 := join_1_0

end S000C02
end Sude.GeneratedTwinScan
