import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S257C14

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S257C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 540934189 widths0 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 540934189 540966957).card = 109 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 540934189 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 540934189 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 540934189 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 540966957 widths1 = 96 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 540966957 540999725).card = 96 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 540966957 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 540966957 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 540966957 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 540999725 widths2 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 540999725 541032493).card = 113 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 540999725 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 540999725 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 540999725 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 541032493 widths3 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 541032493 541065261).card = 112 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 541032493 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 541032493 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 541032493 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 540934189 540999725).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 540934189 ≤ 540966957)
    (by decide : 540966957 ≤ 540999725) block0 block1

theorem join_0_1 : (twinPrimeSegment 540999725 541065261).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 540999725 ≤ 541032493)
    (by decide : 541032493 ≤ 541065261) block2 block3

theorem join_1_0 : (twinPrimeSegment 540934189 541065261).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 540934189 ≤ 540999725)
    (by decide : 540999725 ≤ 541065261) join_0_0 join_0_1

theorem total : (twinPrimeSegment 540934189 541065261).card = 430 := join_1_0

end S257C15
end Sude.GeneratedTwinScan
