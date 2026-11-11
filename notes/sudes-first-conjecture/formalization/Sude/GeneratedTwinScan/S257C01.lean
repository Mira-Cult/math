import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S257C00

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S257C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 539099181 widths0 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 539099181 539131949).card = 113 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 539099181 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 539099181 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 539099181 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 539131949 widths1 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 539131949 539164717).card = 98 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 539131949 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 539131949 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 539131949 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 539164717 widths2 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 539164717 539197485).card = 110 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 539164717 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 539164717 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 539164717 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 539197485 widths3 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 539197485 539230253).card = 115 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 539197485 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 539197485 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 539197485 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 539099181 539164717).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 539099181 ≤ 539131949)
    (by decide : 539131949 ≤ 539164717) block0 block1

theorem join_0_1 : (twinPrimeSegment 539164717 539230253).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 539164717 ≤ 539197485)
    (by decide : 539197485 ≤ 539230253) block2 block3

theorem join_1_0 : (twinPrimeSegment 539099181 539230253).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 539099181 ≤ 539164717)
    (by decide : 539164717 ≤ 539230253) join_0_0 join_0_1

theorem total : (twinPrimeSegment 539099181 539230253).card = 436 := join_1_0

end S257C01
end Sude.GeneratedTwinScan
