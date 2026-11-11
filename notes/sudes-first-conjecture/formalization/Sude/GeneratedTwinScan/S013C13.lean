import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S013C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 28966957 widths0 = 161 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 28966957 28999725).card = 161 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 28966957 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 28966957 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 28966957 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 28999725 widths1 = 151 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 28999725 29032493).card = 151 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 28999725 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 28999725 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 28999725 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 29032493 widths2 = 148 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 29032493 29065261).card = 148 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 29032493 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 29032493 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 29032493 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 29065261 widths3 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 29065261 29098029).card = 137 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 29065261 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 29065261 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 29065261 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 28966957 29032493).card = 312 := by
  simpa using combineTwinPrimeSegments (by decide : 28966957 ≤ 28999725)
    (by decide : 28999725 ≤ 29032493) block0 block1

theorem join_0_1 : (twinPrimeSegment 29032493 29098029).card = 285 := by
  simpa using combineTwinPrimeSegments (by decide : 29032493 ≤ 29065261)
    (by decide : 29065261 ≤ 29098029) block2 block3

theorem join_1_0 : (twinPrimeSegment 28966957 29098029).card = 597 := by
  simpa using combineTwinPrimeSegments (by decide : 28966957 ≤ 29032493)
    (by decide : 29032493 ≤ 29098029) join_0_0 join_0_1

theorem total : (twinPrimeSegment 28966957 29098029).card = 597 := join_1_0

end S013C13
end Sude.GeneratedTwinScan
