import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S001C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 2097197 widths0 = 189 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 2097197 2129965).card = 189 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 2097197 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 2097197 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 2097197 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 2129965 widths1 = 209 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 2129965 2162733).card = 209 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 2129965 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 2129965 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 2129965 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 2162733 widths2 = 201 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 2162733 2195501).card = 201 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 2162733 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 2162733 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 2162733 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 2195501 widths3 = 188 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 2195501 2228269).card = 188 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 2195501 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 2195501 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 2195501 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 2097197 2162733).card = 398 := by
  simpa using combineTwinPrimeSegments (by decide : 2097197 ≤ 2129965)
    (by decide : 2129965 ≤ 2162733) block0 block1

theorem join_0_1 : (twinPrimeSegment 2162733 2228269).card = 389 := by
  simpa using combineTwinPrimeSegments (by decide : 2162733 ≤ 2195501)
    (by decide : 2195501 ≤ 2228269) block2 block3

theorem join_1_0 : (twinPrimeSegment 2097197 2228269).card = 787 := by
  simpa using combineTwinPrimeSegments (by decide : 2097197 ≤ 2162733)
    (by decide : 2162733 ≤ 2228269) join_0_0 join_0_1

theorem total : (twinPrimeSegment 2097197 2228269).card = 787 := join_1_0

end S001C00
end Sude.GeneratedTwinScan
