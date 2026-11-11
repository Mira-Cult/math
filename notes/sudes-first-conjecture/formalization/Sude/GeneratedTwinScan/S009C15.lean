import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S009C14

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S009C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 20840493 widths0 = 165 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 20840493 20873261).card = 165 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 20840493 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 20840493 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 20840493 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 20873261 widths1 = 150 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 20873261 20906029).card = 150 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 20873261 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 20873261 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 20873261 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 20906029 widths2 = 171 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 20906029 20938797).card = 171 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 20906029 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 20906029 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 20906029 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 20938797 widths3 = 140 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 20938797 20971565).card = 140 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 20938797 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 20938797 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 20938797 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 20840493 20906029).card = 315 := by
  simpa using combineTwinPrimeSegments (by decide : 20840493 ≤ 20873261)
    (by decide : 20873261 ≤ 20906029) block0 block1

theorem join_0_1 : (twinPrimeSegment 20906029 20971565).card = 311 := by
  simpa using combineTwinPrimeSegments (by decide : 20906029 ≤ 20938797)
    (by decide : 20938797 ≤ 20971565) block2 block3

theorem join_1_0 : (twinPrimeSegment 20840493 20971565).card = 626 := by
  simpa using combineTwinPrimeSegments (by decide : 20840493 ≤ 20906029)
    (by decide : 20906029 ≤ 20971565) join_0_0 join_0_1

theorem total : (twinPrimeSegment 20840493 20971565).card = 626 := join_1_0

end S009C15
end Sude.GeneratedTwinScan
