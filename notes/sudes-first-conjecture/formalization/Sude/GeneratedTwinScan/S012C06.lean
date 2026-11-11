import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S012C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 25952301 widths0 = 160 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 25952301 25985069).card = 160 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 25952301 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 25952301 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 25952301 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 25985069 widths1 = 142 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 25985069 26017837).card = 142 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 25985069 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 25985069 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 25985069 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 26017837 widths2 = 140 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 26017837 26050605).card = 140 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 26017837 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 26017837 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 26017837 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 26050605 widths3 = 153 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 26050605 26083373).card = 153 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 26050605 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 26050605 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 26050605 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 25952301 26017837).card = 302 := by
  simpa using combineTwinPrimeSegments (by decide : 25952301 ≤ 25985069)
    (by decide : 25985069 ≤ 26017837) block0 block1

theorem join_0_1 : (twinPrimeSegment 26017837 26083373).card = 293 := by
  simpa using combineTwinPrimeSegments (by decide : 26017837 ≤ 26050605)
    (by decide : 26050605 ≤ 26083373) block2 block3

theorem join_1_0 : (twinPrimeSegment 25952301 26083373).card = 595 := by
  simpa using combineTwinPrimeSegments (by decide : 25952301 ≤ 26017837)
    (by decide : 26017837 ≤ 26083373) join_0_0 join_0_1

theorem total : (twinPrimeSegment 25952301 26083373).card = 595 := join_1_0

end S012C06
end Sude.GeneratedTwinScan
