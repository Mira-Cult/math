import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S003C14

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S003C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 8257581 widths0 = 180 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 8257581 8290349).card = 180 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 8257581 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 8257581 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 8257581 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 8290349 widths1 = 162 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 8290349 8323117).card = 162 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 8290349 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 8290349 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 8290349 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 8323117 widths2 = 160 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 8323117 8355885).card = 160 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 8323117 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 8323117 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 8323117 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 8355885 widths3 = 174 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 8355885 8388653).card = 174 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 8355885 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 8355885 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 8355885 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 8257581 8323117).card = 342 := by
  simpa using combineTwinPrimeSegments (by decide : 8257581 ≤ 8290349)
    (by decide : 8290349 ≤ 8323117) block0 block1

theorem join_0_1 : (twinPrimeSegment 8323117 8388653).card = 334 := by
  simpa using combineTwinPrimeSegments (by decide : 8323117 ≤ 8355885)
    (by decide : 8355885 ≤ 8388653) block2 block3

theorem join_1_0 : (twinPrimeSegment 8257581 8388653).card = 676 := by
  simpa using combineTwinPrimeSegments (by decide : 8257581 ≤ 8323117)
    (by decide : 8323117 ≤ 8388653) join_0_0 join_0_1

theorem total : (twinPrimeSegment 8257581 8388653).card = 676 := join_1_0

end S003C15
end Sude.GeneratedTwinScan
