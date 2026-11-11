import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S000C14

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S000C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 1966125 widths0 = 209 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 1966125 1998893).card = 209 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 1966125 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 1966125 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 1966125 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 1998893 widths1 = 223 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 1998893 2031661).card = 223 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 1998893 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 1998893 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 1998893 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 2031661 widths2 = 208 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 2031661 2064429).card = 208 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 2031661 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 2031661 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 2031661 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 2064429 widths3 = 205 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 2064429 2097197).card = 205 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 2064429 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 2064429 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 2064429 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 1966125 2031661).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 1966125 ≤ 1998893)
    (by decide : 1998893 ≤ 2031661) block0 block1

theorem join_0_1 : (twinPrimeSegment 2031661 2097197).card = 413 := by
  simpa using combineTwinPrimeSegments (by decide : 2031661 ≤ 2064429)
    (by decide : 2064429 ≤ 2097197) block2 block3

theorem join_1_0 : (twinPrimeSegment 1966125 2097197).card = 845 := by
  simpa using combineTwinPrimeSegments (by decide : 1966125 ≤ 2031661)
    (by decide : 2031661 ≤ 2097197) join_0_0 join_0_1

theorem total : (twinPrimeSegment 1966125 2097197).card = 845 := join_1_0

end S000C15
end Sude.GeneratedTwinScan
