import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S001C03

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S001C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 2621485 widths0 = 198 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 2621485 2654253).card = 198 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 2621485 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 2621485 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 2621485 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 2654253 widths1 = 200 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 2654253 2687021).card = 200 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 2654253 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 2654253 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 2654253 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 2687021 widths2 = 209 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 2687021 2719789).card = 209 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 2687021 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 2687021 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 2687021 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 2719789 widths3 = 192 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 2719789 2752557).card = 192 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 2719789 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 2719789 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 2719789 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 2621485 2687021).card = 398 := by
  simpa using combineTwinPrimeSegments (by decide : 2621485 ≤ 2654253)
    (by decide : 2654253 ≤ 2687021) block0 block1

theorem join_0_1 : (twinPrimeSegment 2687021 2752557).card = 401 := by
  simpa using combineTwinPrimeSegments (by decide : 2687021 ≤ 2719789)
    (by decide : 2719789 ≤ 2752557) block2 block3

theorem join_1_0 : (twinPrimeSegment 2621485 2752557).card = 799 := by
  simpa using combineTwinPrimeSegments (by decide : 2621485 ≤ 2687021)
    (by decide : 2687021 ≤ 2752557) join_0_0 join_0_1

theorem total : (twinPrimeSegment 2621485 2752557).card = 799 := join_1_0

end S001C04
end Sude.GeneratedTwinScan
