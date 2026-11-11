import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S001C02

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S001C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 2490413 widths0 = 181 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 2490413 2523181).card = 181 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 2490413 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 2490413 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 2490413 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 2523181 widths1 = 192 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 2523181 2555949).card = 192 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 2523181 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 2523181 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 2523181 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 2555949 widths2 = 213 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 2555949 2588717).card = 213 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 2555949 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 2555949 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 2555949 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 2588717 widths3 = 201 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 2588717 2621485).card = 201 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 2588717 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 2588717 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 2588717 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 2490413 2555949).card = 373 := by
  simpa using combineTwinPrimeSegments (by decide : 2490413 ≤ 2523181)
    (by decide : 2523181 ≤ 2555949) block0 block1

theorem join_0_1 : (twinPrimeSegment 2555949 2621485).card = 414 := by
  simpa using combineTwinPrimeSegments (by decide : 2555949 ≤ 2588717)
    (by decide : 2588717 ≤ 2621485) block2 block3

theorem join_1_0 : (twinPrimeSegment 2490413 2621485).card = 787 := by
  simpa using combineTwinPrimeSegments (by decide : 2490413 ≤ 2555949)
    (by decide : 2555949 ≤ 2621485) join_0_0 join_0_1

theorem total : (twinPrimeSegment 2490413 2621485).card = 787 := join_1_0

end S001C03
end Sude.GeneratedTwinScan
