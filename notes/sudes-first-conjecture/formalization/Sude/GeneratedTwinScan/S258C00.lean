import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S258C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 541065261 widths0 = 95 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 541065261 541098029).card = 95 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 541065261 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 541065261 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 541065261 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 541098029 widths1 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 541098029 541130797).card = 111 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 541098029 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 541098029 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 541098029 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 541130797 widths2 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 541130797 541163565).card = 108 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 541130797 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 541130797 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 541130797 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 541163565 widths3 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 541163565 541196333).card = 110 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 541163565 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 541163565 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 541163565 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 541065261 541130797).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 541065261 ≤ 541098029)
    (by decide : 541098029 ≤ 541130797) block0 block1

theorem join_0_1 : (twinPrimeSegment 541130797 541196333).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 541130797 ≤ 541163565)
    (by decide : 541163565 ≤ 541196333) block2 block3

theorem join_1_0 : (twinPrimeSegment 541065261 541196333).card = 424 := by
  simpa using combineTwinPrimeSegments (by decide : 541065261 ≤ 541130797)
    (by decide : 541130797 ≤ 541196333) join_0_0 join_0_1

theorem total : (twinPrimeSegment 541065261 541196333).card = 424 := join_1_0

end S258C00
end Sude.GeneratedTwinScan
