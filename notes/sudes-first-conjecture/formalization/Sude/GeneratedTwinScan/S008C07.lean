import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S008C06

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S008C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 17694765 widths0 = 160 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 17694765 17727533).card = 160 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 17694765 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 17694765 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 17694765 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 17727533 widths1 = 172 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 17727533 17760301).card = 172 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 17727533 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 17727533 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 17727533 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 17760301 widths2 = 171 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 17760301 17793069).card = 171 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 17760301 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 17760301 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 17760301 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 17793069 widths3 = 164 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 17793069 17825837).card = 164 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 17793069 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 17793069 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 17793069 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 17694765 17760301).card = 332 := by
  simpa using combineTwinPrimeSegments (by decide : 17694765 ≤ 17727533)
    (by decide : 17727533 ≤ 17760301) block0 block1

theorem join_0_1 : (twinPrimeSegment 17760301 17825837).card = 335 := by
  simpa using combineTwinPrimeSegments (by decide : 17760301 ≤ 17793069)
    (by decide : 17793069 ≤ 17825837) block2 block3

theorem join_1_0 : (twinPrimeSegment 17694765 17825837).card = 667 := by
  simpa using combineTwinPrimeSegments (by decide : 17694765 ≤ 17760301)
    (by decide : 17760301 ≤ 17825837) join_0_0 join_0_1

theorem total : (twinPrimeSegment 17694765 17825837).card = 667 := join_1_0

end S008C07
end Sude.GeneratedTwinScan
