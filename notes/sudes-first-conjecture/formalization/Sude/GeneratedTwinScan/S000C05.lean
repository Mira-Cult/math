import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S000C04

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S000C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 655405 widths0 = 237 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 655405 688173).card = 237 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 655405 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 655405 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 655405 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 688173 widths1 = 222 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 688173 720941).card = 222 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 688173 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 688173 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 688173 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 720941 widths2 = 228 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 720941 753709).card = 228 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 720941 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 720941 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 720941 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 753709 widths3 = 231 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 753709 786477).card = 231 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 753709 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 753709 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 753709 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 655405 720941).card = 459 := by
  simpa using combineTwinPrimeSegments (by decide : 655405 ≤ 688173)
    (by decide : 688173 ≤ 720941) block0 block1

theorem join_0_1 : (twinPrimeSegment 720941 786477).card = 459 := by
  simpa using combineTwinPrimeSegments (by decide : 720941 ≤ 753709)
    (by decide : 753709 ≤ 786477) block2 block3

theorem join_1_0 : (twinPrimeSegment 655405 786477).card = 918 := by
  simpa using combineTwinPrimeSegments (by decide : 655405 ≤ 720941)
    (by decide : 720941 ≤ 786477) join_0_0 join_0_1

theorem total : (twinPrimeSegment 655405 786477).card = 918 := join_1_0

end S000C05
end Sude.GeneratedTwinScan
