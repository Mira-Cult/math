import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S000C12

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S000C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 1703981 widths0 = 214 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 1703981 1736749).card = 214 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 1703981 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 1703981 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 1703981 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 1736749 widths1 = 211 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 1736749 1769517).card = 211 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 1736749 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 1736749 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 1736749 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 1769517 widths2 = 210 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 1769517 1802285).card = 210 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 1769517 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 1769517 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 1769517 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 1802285 widths3 = 228 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 1802285 1835053).card = 228 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 1802285 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 1802285 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 1802285 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 1703981 1769517).card = 425 := by
  simpa using combineTwinPrimeSegments (by decide : 1703981 ≤ 1736749)
    (by decide : 1736749 ≤ 1769517) block0 block1

theorem join_0_1 : (twinPrimeSegment 1769517 1835053).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 1769517 ≤ 1802285)
    (by decide : 1802285 ≤ 1835053) block2 block3

theorem join_1_0 : (twinPrimeSegment 1703981 1835053).card = 863 := by
  simpa using combineTwinPrimeSegments (by decide : 1703981 ≤ 1769517)
    (by decide : 1769517 ≤ 1835053) join_0_0 join_0_1

theorem total : (twinPrimeSegment 1703981 1835053).card = 863 := join_1_0

end S000C13
end Sude.GeneratedTwinScan
