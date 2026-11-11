import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S014C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 31326253 widths0 = 145 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 31326253 31359021).card = 145 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 31326253 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 31326253 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 31326253 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 31359021 widths1 = 146 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 31359021 31391789).card = 146 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 31359021 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 31359021 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 31359021 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 31391789 widths2 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 31391789 31424557).card = 124 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 31391789 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 31391789 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 31391789 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 31424557 widths3 = 158 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 31424557 31457325).card = 158 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 31424557 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 31424557 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 31424557 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 31326253 31391789).card = 291 := by
  simpa using combineTwinPrimeSegments (by decide : 31326253 ≤ 31359021)
    (by decide : 31359021 ≤ 31391789) block0 block1

theorem join_0_1 : (twinPrimeSegment 31391789 31457325).card = 282 := by
  simpa using combineTwinPrimeSegments (by decide : 31391789 ≤ 31424557)
    (by decide : 31424557 ≤ 31457325) block2 block3

theorem join_1_0 : (twinPrimeSegment 31326253 31457325).card = 573 := by
  simpa using combineTwinPrimeSegments (by decide : 31326253 ≤ 31391789)
    (by decide : 31391789 ≤ 31457325) join_0_0 join_0_1

theorem total : (twinPrimeSegment 31326253 31457325).card = 573 := join_1_0

end S014C15
end Sude.GeneratedTwinScan
