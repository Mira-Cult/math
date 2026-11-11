import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S017C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 35651629 widths0 = 151 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 35651629 35684397).card = 151 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 35651629 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 35684397 widths1 = 143 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 35684397 35717165).card = 143 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 35684397 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 35717165 widths2 = 143 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 35717165 35749933).card = 143 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 35717165 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 35749933 widths3 = 164 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 35749933 35782701).card = 164 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 35749933 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 35651629 35717165).card = 294 := by
  simpa using combineTwinPrimeSegments (by decide : 35651629 ≤ 35684397)
    (by decide : 35684397 ≤ 35717165) block0 block1

theorem join_0_1 : (twinPrimeSegment 35717165 35782701).card = 307 := by
  simpa using combineTwinPrimeSegments (by decide : 35717165 ≤ 35749933)
    (by decide : 35749933 ≤ 35782701) block2 block3

theorem join_1_0 : (twinPrimeSegment 35651629 35782701).card = 601 := by
  simpa using combineTwinPrimeSegments (by decide : 35651629 ≤ 35717165)
    (by decide : 35717165 ≤ 35782701) join_0_0 join_0_1

theorem total : (twinPrimeSegment 35651629 35782701).card = 601 := join_1_0

end S017C00
end Sude.GeneratedTwinScan
