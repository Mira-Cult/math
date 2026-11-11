import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S007C14

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S007C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 16646189 widths0 = 144 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 16646189 16678957).card = 144 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 16646189 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 16646189 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 16646189 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 16678957 widths1 = 152 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 16678957 16711725).card = 152 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 16678957 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 16678957 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 16678957 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 16711725 widths2 = 158 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 16711725 16744493).card = 158 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 16711725 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 16711725 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 16711725 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 16744493 widths3 = 158 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 16744493 16777261).card = 158 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 16744493 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 16744493 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 16744493 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 16646189 16711725).card = 296 := by
  simpa using combineTwinPrimeSegments (by decide : 16646189 ≤ 16678957)
    (by decide : 16678957 ≤ 16711725) block0 block1

theorem join_0_1 : (twinPrimeSegment 16711725 16777261).card = 316 := by
  simpa using combineTwinPrimeSegments (by decide : 16711725 ≤ 16744493)
    (by decide : 16744493 ≤ 16777261) block2 block3

theorem join_1_0 : (twinPrimeSegment 16646189 16777261).card = 612 := by
  simpa using combineTwinPrimeSegments (by decide : 16646189 ≤ 16711725)
    (by decide : 16711725 ≤ 16777261) join_0_0 join_0_1

theorem total : (twinPrimeSegment 16646189 16777261).card = 612 := join_1_0

end S007C15
end Sude.GeneratedTwinScan
