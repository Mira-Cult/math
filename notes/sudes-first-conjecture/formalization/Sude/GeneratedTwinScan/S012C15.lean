import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S012C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 27131949 widths0 = 149 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 27131949 27164717).card = 149 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 27131949 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 27131949 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 27131949 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 27164717 widths1 = 149 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 27164717 27197485).card = 149 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 27164717 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 27164717 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 27164717 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 27197485 widths2 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 27197485 27230253).card = 138 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 27197485 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 27197485 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 27197485 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 27230253 widths3 = 142 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 27230253 27263021).card = 142 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 27230253 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 27230253 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 27230253 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 27131949 27197485).card = 298 := by
  simpa using combineTwinPrimeSegments (by decide : 27131949 ≤ 27164717)
    (by decide : 27164717 ≤ 27197485) block0 block1

theorem join_0_1 : (twinPrimeSegment 27197485 27263021).card = 280 := by
  simpa using combineTwinPrimeSegments (by decide : 27197485 ≤ 27230253)
    (by decide : 27230253 ≤ 27263021) block2 block3

theorem join_1_0 : (twinPrimeSegment 27131949 27263021).card = 578 := by
  simpa using combineTwinPrimeSegments (by decide : 27131949 ≤ 27197485)
    (by decide : 27197485 ≤ 27263021) join_0_0 join_0_1

theorem total : (twinPrimeSegment 27131949 27263021).card = 578 := join_1_0

end S012C15
end Sude.GeneratedTwinScan
