import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S011C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 24641581 widths0 = 142 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 24641581 24674349).card = 142 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 24641581 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 24641581 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 24641581 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 24674349 widths1 = 164 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 24674349 24707117).card = 164 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 24674349 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 24674349 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 24674349 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 24707117 widths2 = 164 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 24707117 24739885).card = 164 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 24707117 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 24707117 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 24707117 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 24739885 widths3 = 157 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 24739885 24772653).card = 157 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 24739885 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 24739885 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 24739885 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 24641581 24707117).card = 306 := by
  simpa using combineTwinPrimeSegments (by decide : 24641581 ≤ 24674349)
    (by decide : 24674349 ≤ 24707117) block0 block1

theorem join_0_1 : (twinPrimeSegment 24707117 24772653).card = 321 := by
  simpa using combineTwinPrimeSegments (by decide : 24707117 ≤ 24739885)
    (by decide : 24739885 ≤ 24772653) block2 block3

theorem join_1_0 : (twinPrimeSegment 24641581 24772653).card = 627 := by
  simpa using combineTwinPrimeSegments (by decide : 24641581 ≤ 24707117)
    (by decide : 24707117 ≤ 24772653) join_0_0 join_0_1

theorem total : (twinPrimeSegment 24641581 24772653).card = 627 := join_1_0

end S011C12
end Sude.GeneratedTwinScan
