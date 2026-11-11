import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S013C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 28573741 widths0 = 141 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 28573741 28606509).card = 141 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 28573741 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 28573741 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 28573741 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 28606509 widths1 = 144 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 28606509 28639277).card = 144 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 28606509 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 28606509 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 28606509 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 28639277 widths2 = 147 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 28639277 28672045).card = 147 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 28639277 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 28639277 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 28639277 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 28672045 widths3 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 28672045 28704813).card = 133 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 28672045 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 28672045 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 28672045 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 28573741 28639277).card = 285 := by
  simpa using combineTwinPrimeSegments (by decide : 28573741 ≤ 28606509)
    (by decide : 28606509 ≤ 28639277) block0 block1

theorem join_0_1 : (twinPrimeSegment 28639277 28704813).card = 280 := by
  simpa using combineTwinPrimeSegments (by decide : 28639277 ≤ 28672045)
    (by decide : 28672045 ≤ 28704813) block2 block3

theorem join_1_0 : (twinPrimeSegment 28573741 28704813).card = 565 := by
  simpa using combineTwinPrimeSegments (by decide : 28573741 ≤ 28639277)
    (by decide : 28639277 ≤ 28704813) join_0_0 join_0_1

theorem total : (twinPrimeSegment 28573741 28704813).card = 565 := join_1_0

end S013C10
end Sude.GeneratedTwinScan
