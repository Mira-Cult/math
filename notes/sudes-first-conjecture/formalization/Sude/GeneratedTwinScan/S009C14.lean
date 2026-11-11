import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S009C13

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S009C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 20709421 widths0 = 165 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 20709421 20742189).card = 165 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 20709421 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 20709421 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 20709421 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 20742189 widths1 = 147 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 20742189 20774957).card = 147 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 20742189 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 20742189 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 20742189 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 20774957 widths2 = 151 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 20774957 20807725).card = 151 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 20774957 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 20774957 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 20774957 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 20807725 widths3 = 147 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 20807725 20840493).card = 147 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 20807725 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 20807725 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 20807725 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 20709421 20774957).card = 312 := by
  simpa using combineTwinPrimeSegments (by decide : 20709421 ≤ 20742189)
    (by decide : 20742189 ≤ 20774957) block0 block1

theorem join_0_1 : (twinPrimeSegment 20774957 20840493).card = 298 := by
  simpa using combineTwinPrimeSegments (by decide : 20774957 ≤ 20807725)
    (by decide : 20807725 ≤ 20840493) block2 block3

theorem join_1_0 : (twinPrimeSegment 20709421 20840493).card = 610 := by
  simpa using combineTwinPrimeSegments (by decide : 20709421 ≤ 20774957)
    (by decide : 20774957 ≤ 20840493) join_0_0 join_0_1

theorem total : (twinPrimeSegment 20709421 20840493).card = 610 := join_1_0

end S009C14
end Sude.GeneratedTwinScan
