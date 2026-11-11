import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S006C14

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S006C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 14549037 widths0 = 172 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 14549037 14581805).card = 172 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 14549037 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 14549037 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 14549037 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 14581805 widths1 = 159 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 14581805 14614573).card = 159 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 14581805 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 14581805 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 14581805 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 14614573 widths2 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 14614573 14647341).card = 137 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 14614573 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 14614573 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 14614573 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 14647341 widths3 = 165 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 14647341 14680109).card = 165 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 14647341 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 14647341 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 14647341 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 14549037 14614573).card = 331 := by
  simpa using combineTwinPrimeSegments (by decide : 14549037 ≤ 14581805)
    (by decide : 14581805 ≤ 14614573) block0 block1

theorem join_0_1 : (twinPrimeSegment 14614573 14680109).card = 302 := by
  simpa using combineTwinPrimeSegments (by decide : 14614573 ≤ 14647341)
    (by decide : 14647341 ≤ 14680109) block2 block3

theorem join_1_0 : (twinPrimeSegment 14549037 14680109).card = 633 := by
  simpa using combineTwinPrimeSegments (by decide : 14549037 ≤ 14614573)
    (by decide : 14614573 ≤ 14680109) join_0_0 join_0_1

theorem total : (twinPrimeSegment 14549037 14680109).card = 633 := join_1_0

end S006C15
end Sude.GeneratedTwinScan
