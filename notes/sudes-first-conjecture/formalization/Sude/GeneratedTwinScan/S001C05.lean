import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S001C04

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S001C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 2752557 widths0 = 191 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 2752557 2785325).card = 191 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 2752557 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 2752557 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 2752557 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 2785325 widths1 = 199 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 2785325 2818093).card = 199 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 2785325 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 2785325 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 2785325 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 2818093 widths2 = 198 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 2818093 2850861).card = 198 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 2818093 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 2818093 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 2818093 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 2850861 widths3 = 179 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 2850861 2883629).card = 179 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 2850861 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 2850861 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 2850861 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 2752557 2818093).card = 390 := by
  simpa using combineTwinPrimeSegments (by decide : 2752557 ≤ 2785325)
    (by decide : 2785325 ≤ 2818093) block0 block1

theorem join_0_1 : (twinPrimeSegment 2818093 2883629).card = 377 := by
  simpa using combineTwinPrimeSegments (by decide : 2818093 ≤ 2850861)
    (by decide : 2850861 ≤ 2883629) block2 block3

theorem join_1_0 : (twinPrimeSegment 2752557 2883629).card = 767 := by
  simpa using combineTwinPrimeSegments (by decide : 2752557 ≤ 2818093)
    (by decide : 2818093 ≤ 2883629) join_0_0 join_0_1

theorem total : (twinPrimeSegment 2752557 2883629).card = 767 := join_1_0

end S001C05
end Sude.GeneratedTwinScan
