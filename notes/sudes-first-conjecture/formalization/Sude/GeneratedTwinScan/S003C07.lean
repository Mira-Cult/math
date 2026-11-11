import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S003C06

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S003C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 7209005 widths0 = 169 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 7209005 7241773).card = 169 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 7209005 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 7209005 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 7209005 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 7241773 widths1 = 170 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 7241773 7274541).card = 170 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 7241773 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 7241773 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 7241773 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 7274541 widths2 = 179 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 7274541 7307309).card = 179 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 7274541 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 7274541 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 7274541 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 7307309 widths3 = 173 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 7307309 7340077).card = 173 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 7307309 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 7307309 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 7307309 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 7209005 7274541).card = 339 := by
  simpa using combineTwinPrimeSegments (by decide : 7209005 ≤ 7241773)
    (by decide : 7241773 ≤ 7274541) block0 block1

theorem join_0_1 : (twinPrimeSegment 7274541 7340077).card = 352 := by
  simpa using combineTwinPrimeSegments (by decide : 7274541 ≤ 7307309)
    (by decide : 7307309 ≤ 7340077) block2 block3

theorem join_1_0 : (twinPrimeSegment 7209005 7340077).card = 691 := by
  simpa using combineTwinPrimeSegments (by decide : 7209005 ≤ 7274541)
    (by decide : 7274541 ≤ 7340077) join_0_0 join_0_1

theorem total : (twinPrimeSegment 7209005 7340077).card = 691 := join_1_0

end S003C07
end Sude.GeneratedTwinScan
