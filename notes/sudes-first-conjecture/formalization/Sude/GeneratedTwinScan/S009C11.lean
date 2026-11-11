import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S009C10

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S009C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 20316205 widths0 = 150 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 20316205 20348973).card = 150 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 20316205 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 20316205 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 20316205 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 20348973 widths1 = 156 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 20348973 20381741).card = 156 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 20348973 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 20348973 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 20348973 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 20381741 widths2 = 155 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 20381741 20414509).card = 155 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 20381741 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 20381741 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 20381741 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 20414509 widths3 = 165 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 20414509 20447277).card = 165 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 20414509 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 20414509 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 20414509 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 20316205 20381741).card = 306 := by
  simpa using combineTwinPrimeSegments (by decide : 20316205 ≤ 20348973)
    (by decide : 20348973 ≤ 20381741) block0 block1

theorem join_0_1 : (twinPrimeSegment 20381741 20447277).card = 320 := by
  simpa using combineTwinPrimeSegments (by decide : 20381741 ≤ 20414509)
    (by decide : 20414509 ≤ 20447277) block2 block3

theorem join_1_0 : (twinPrimeSegment 20316205 20447277).card = 626 := by
  simpa using combineTwinPrimeSegments (by decide : 20316205 ≤ 20381741)
    (by decide : 20381741 ≤ 20447277) join_0_0 join_0_1

theorem total : (twinPrimeSegment 20316205 20447277).card = 626 := join_1_0

end S009C11
end Sude.GeneratedTwinScan
