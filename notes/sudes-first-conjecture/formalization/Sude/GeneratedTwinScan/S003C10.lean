import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S003C09

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S003C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 7602221 widths0 = 179 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 7602221 7634989).card = 179 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 7602221 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 7602221 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 7602221 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 7634989 widths1 = 161 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 7634989 7667757).card = 161 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 7634989 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 7634989 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 7634989 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 7667757 widths2 = 183 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 7667757 7700525).card = 183 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 7667757 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 7667757 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 7667757 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 7700525 widths3 = 176 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 7700525 7733293).card = 176 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 7700525 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 7700525 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 7700525 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 7602221 7667757).card = 340 := by
  simpa using combineTwinPrimeSegments (by decide : 7602221 ≤ 7634989)
    (by decide : 7634989 ≤ 7667757) block0 block1

theorem join_0_1 : (twinPrimeSegment 7667757 7733293).card = 359 := by
  simpa using combineTwinPrimeSegments (by decide : 7667757 ≤ 7700525)
    (by decide : 7700525 ≤ 7733293) block2 block3

theorem join_1_0 : (twinPrimeSegment 7602221 7733293).card = 699 := by
  simpa using combineTwinPrimeSegments (by decide : 7602221 ≤ 7667757)
    (by decide : 7667757 ≤ 7733293) join_0_0 join_0_1

theorem total : (twinPrimeSegment 7602221 7733293).card = 699 := join_1_0

end S003C10
end Sude.GeneratedTwinScan
