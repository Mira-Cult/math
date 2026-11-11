import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S026C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 55574573 widths0 = 146 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 55574573 55607341).card = 146 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 55574573 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 55607341 widths1 = 138 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 55607341 55640109).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 55607341 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 55640109 widths2 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 55640109 55672877).card = 132 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 55640109 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 55672877 widths3 = 157 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 55672877 55705645).card = 157 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 55672877 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 55574573 55640109).card = 284 := by
  simpa using combineTwinPrimeSegments (by decide : 55574573 ≤ 55607341)
    (by decide : 55607341 ≤ 55640109) block0 block1

theorem join_0_1 : (twinPrimeSegment 55640109 55705645).card = 289 := by
  simpa using combineTwinPrimeSegments (by decide : 55640109 ≤ 55672877)
    (by decide : 55672877 ≤ 55705645) block2 block3

theorem join_1_0 : (twinPrimeSegment 55574573 55705645).card = 573 := by
  simpa using combineTwinPrimeSegments (by decide : 55574573 ≤ 55640109)
    (by decide : 55640109 ≤ 55705645) join_0_0 join_0_1

theorem total : (twinPrimeSegment 55574573 55705645).card = 573 := join_1_0

end S026C08
end Sude.GeneratedTwinScan
