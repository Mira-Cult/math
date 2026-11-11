import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S000C03

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S000C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 524333 widths0 = 248 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 524333 557101).card = 248 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 524333 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 524333 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 524333 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 557101 widths1 = 258 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 557101 589869).card = 258 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 557101 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 557101 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 557101 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 589869 widths2 = 244 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 589869 622637).card = 244 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 589869 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 589869 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 589869 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 622637 widths3 = 250 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 622637 655405).card = 250 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 622637 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 622637 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 622637 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 524333 589869).card = 506 := by
  simpa using combineTwinPrimeSegments (by decide : 524333 ≤ 557101)
    (by decide : 557101 ≤ 589869) block0 block1

theorem join_0_1 : (twinPrimeSegment 589869 655405).card = 494 := by
  simpa using combineTwinPrimeSegments (by decide : 589869 ≤ 622637)
    (by decide : 622637 ≤ 655405) block2 block3

theorem join_1_0 : (twinPrimeSegment 524333 655405).card = 1000 := by
  simpa using combineTwinPrimeSegments (by decide : 524333 ≤ 589869)
    (by decide : 589869 ≤ 655405) join_0_0 join_0_1

theorem total : (twinPrimeSegment 524333 655405).card = 1000 := join_1_0

end S000C04
end Sude.GeneratedTwinScan
