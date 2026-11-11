import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S021C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 44957741 widths0 = 139 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 44957741 44990509).card = 139 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 44957741 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 44990509 widths1 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 44990509 45023277).card = 131 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 44990509 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 45023277 widths2 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 45023277 45056045).card = 132 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 45023277 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 45056045 widths3 = 158 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 45056045 45088813).card = 158 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 45056045 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 44957741 45023277).card = 270 := by
  simpa using combineTwinPrimeSegments (by decide : 44957741 ≤ 44990509)
    (by decide : 44990509 ≤ 45023277) block0 block1

theorem join_0_1 : (twinPrimeSegment 45023277 45088813).card = 290 := by
  simpa using combineTwinPrimeSegments (by decide : 45023277 ≤ 45056045)
    (by decide : 45056045 ≤ 45088813) block2 block3

theorem join_1_0 : (twinPrimeSegment 44957741 45088813).card = 560 := by
  simpa using combineTwinPrimeSegments (by decide : 44957741 ≤ 45023277)
    (by decide : 45023277 ≤ 45088813) join_0_0 join_0_1

theorem total : (twinPrimeSegment 44957741 45088813).card = 560 := join_1_0

end S021C07
end Sude.GeneratedTwinScan
