import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S010C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 22806573 widths0 = 142 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 22806573 22839341).card = 142 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 22806573 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 22806573 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 22806573 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 22839341 widths1 = 153 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 22839341 22872109).card = 153 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 22839341 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 22839341 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 22839341 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 22872109 widths2 = 151 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 22872109 22904877).card = 151 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 22872109 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 22872109 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 22872109 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 22904877 widths3 = 146 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 22904877 22937645).card = 146 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 22904877 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 22904877 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 22904877 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 22806573 22872109).card = 295 := by
  simpa using combineTwinPrimeSegments (by decide : 22806573 ≤ 22839341)
    (by decide : 22839341 ≤ 22872109) block0 block1

theorem join_0_1 : (twinPrimeSegment 22872109 22937645).card = 297 := by
  simpa using combineTwinPrimeSegments (by decide : 22872109 ≤ 22904877)
    (by decide : 22904877 ≤ 22937645) block2 block3

theorem join_1_0 : (twinPrimeSegment 22806573 22937645).card = 592 := by
  simpa using combineTwinPrimeSegments (by decide : 22806573 ≤ 22872109)
    (by decide : 22872109 ≤ 22937645) join_0_0 join_0_1

theorem total : (twinPrimeSegment 22806573 22937645).card = 592 := join_1_0

end S010C14
end Sude.GeneratedTwinScan
