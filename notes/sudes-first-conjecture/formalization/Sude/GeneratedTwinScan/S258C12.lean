import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S258C11

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S258C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 542638125 widths0 = 97 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 542638125 542670893).card = 97 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 542638125 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 542638125 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 542638125 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 542670893 widths1 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 542670893 542703661).card = 112 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 542670893 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 542670893 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 542670893 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 542703661 widths2 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 542703661 542736429).card = 101 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 542703661 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 542703661 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 542703661 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 542736429 widths3 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 542736429 542769197).card = 132 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 542736429 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 542736429 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 542736429 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 542638125 542703661).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 542638125 ≤ 542670893)
    (by decide : 542670893 ≤ 542703661) block0 block1

theorem join_0_1 : (twinPrimeSegment 542703661 542769197).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 542703661 ≤ 542736429)
    (by decide : 542736429 ≤ 542769197) block2 block3

theorem join_1_0 : (twinPrimeSegment 542638125 542769197).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 542638125 ≤ 542703661)
    (by decide : 542703661 ≤ 542769197) join_0_0 join_0_1

theorem total : (twinPrimeSegment 542638125 542769197).card = 442 := join_1_0

end S258C12
end Sude.GeneratedTwinScan
