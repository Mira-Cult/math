import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S004C02

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S004C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 8781869 widths0 = 167 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 8781869 8814637).card = 167 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 8781869 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 8781869 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 8781869 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 8814637 widths1 = 163 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 8814637 8847405).card = 163 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 8814637 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 8814637 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 8814637 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 8847405 widths2 = 173 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 8847405 8880173).card = 173 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 8847405 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 8847405 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 8847405 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 8880173 widths3 = 171 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 8880173 8912941).card = 171 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 8880173 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 8880173 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 8880173 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 8781869 8847405).card = 330 := by
  simpa using combineTwinPrimeSegments (by decide : 8781869 ≤ 8814637)
    (by decide : 8814637 ≤ 8847405) block0 block1

theorem join_0_1 : (twinPrimeSegment 8847405 8912941).card = 344 := by
  simpa using combineTwinPrimeSegments (by decide : 8847405 ≤ 8880173)
    (by decide : 8880173 ≤ 8912941) block2 block3

theorem join_1_0 : (twinPrimeSegment 8781869 8912941).card = 674 := by
  simpa using combineTwinPrimeSegments (by decide : 8781869 ≤ 8847405)
    (by decide : 8847405 ≤ 8912941) join_0_0 join_0_1

theorem total : (twinPrimeSegment 8781869 8912941).card = 674 := join_1_0

end S004C03
end Sude.GeneratedTwinScan
