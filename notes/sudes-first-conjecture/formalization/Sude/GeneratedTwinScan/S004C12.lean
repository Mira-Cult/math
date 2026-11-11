import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S004C11

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S004C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 9961517 widths0 = 165 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 9961517 9994285).card = 165 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 9961517 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 9961517 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 9961517 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 9994285 widths1 = 178 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 9994285 10027053).card = 178 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 9994285 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 9994285 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 9994285 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 10027053 widths2 = 163 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 10027053 10059821).card = 163 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 10027053 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 10027053 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 10027053 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 10059821 widths3 = 168 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 10059821 10092589).card = 168 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 10059821 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 10059821 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 10059821 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 9961517 10027053).card = 343 := by
  simpa using combineTwinPrimeSegments (by decide : 9961517 ≤ 9994285)
    (by decide : 9994285 ≤ 10027053) block0 block1

theorem join_0_1 : (twinPrimeSegment 10027053 10092589).card = 331 := by
  simpa using combineTwinPrimeSegments (by decide : 10027053 ≤ 10059821)
    (by decide : 10059821 ≤ 10092589) block2 block3

theorem join_1_0 : (twinPrimeSegment 9961517 10092589).card = 674 := by
  simpa using combineTwinPrimeSegments (by decide : 9961517 ≤ 10027053)
    (by decide : 10027053 ≤ 10092589) join_0_0 join_0_1

theorem total : (twinPrimeSegment 9961517 10092589).card = 674 := join_1_0

end S004C12
end Sude.GeneratedTwinScan
