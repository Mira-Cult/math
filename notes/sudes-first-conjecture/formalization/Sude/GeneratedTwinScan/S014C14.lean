import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S014C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 31195181 widths0 = 142 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 31195181 31227949).card = 142 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 31195181 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 31195181 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 31195181 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 31227949 widths1 = 155 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 31227949 31260717).card = 155 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 31227949 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 31227949 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 31227949 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 31260717 widths2 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 31260717 31293485).card = 138 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 31260717 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 31260717 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 31260717 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 31293485 widths3 = 146 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 31293485 31326253).card = 146 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 31293485 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 31293485 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 31293485 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 31195181 31260717).card = 297 := by
  simpa using combineTwinPrimeSegments (by decide : 31195181 ≤ 31227949)
    (by decide : 31227949 ≤ 31260717) block0 block1

theorem join_0_1 : (twinPrimeSegment 31260717 31326253).card = 284 := by
  simpa using combineTwinPrimeSegments (by decide : 31260717 ≤ 31293485)
    (by decide : 31293485 ≤ 31326253) block2 block3

theorem join_1_0 : (twinPrimeSegment 31195181 31326253).card = 581 := by
  simpa using combineTwinPrimeSegments (by decide : 31195181 ≤ 31260717)
    (by decide : 31260717 ≤ 31326253) join_0_0 join_0_1

theorem total : (twinPrimeSegment 31195181 31326253).card = 581 := join_1_0

end S014C14
end Sude.GeneratedTwinScan
