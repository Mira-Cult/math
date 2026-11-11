import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S020C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 43909165 widths0 = 140 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 43909165 43941933).card = 140 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 43909165 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 43941933 widths1 = 144 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 43941933 43974701).card = 144 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 43941933 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 43974701 widths2 = 141 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 43974701 44007469).card = 141 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 43974701 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 44007469 widths3 = 140 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 44007469 44040237).card = 140 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 44007469 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 43909165 43974701).card = 284 := by
  simpa using combineTwinPrimeSegments (by decide : 43909165 ≤ 43941933)
    (by decide : 43941933 ≤ 43974701) block0 block1

theorem join_0_1 : (twinPrimeSegment 43974701 44040237).card = 281 := by
  simpa using combineTwinPrimeSegments (by decide : 43974701 ≤ 44007469)
    (by decide : 44007469 ≤ 44040237) block2 block3

theorem join_1_0 : (twinPrimeSegment 43909165 44040237).card = 565 := by
  simpa using combineTwinPrimeSegments (by decide : 43909165 ≤ 43974701)
    (by decide : 43974701 ≤ 44040237) join_0_0 join_0_1

theorem total : (twinPrimeSegment 43909165 44040237).card = 565 := join_1_0

end S020C15
end Sude.GeneratedTwinScan
