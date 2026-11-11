import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S016C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 35258413 widths0 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 35258413 35291181).card = 135 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 35258413 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 35291181 widths1 = 155 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 35291181 35323949).card = 155 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 35291181 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 35323949 widths2 = 149 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 35323949 35356717).card = 149 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 35323949 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 35356717 widths3 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 35356717 35389485).card = 127 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 35356717 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 35258413 35323949).card = 290 := by
  simpa using combineTwinPrimeSegments (by decide : 35258413 ≤ 35291181)
    (by decide : 35291181 ≤ 35323949) block0 block1

theorem join_0_1 : (twinPrimeSegment 35323949 35389485).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 35323949 ≤ 35356717)
    (by decide : 35356717 ≤ 35389485) block2 block3

theorem join_1_0 : (twinPrimeSegment 35258413 35389485).card = 566 := by
  simpa using combineTwinPrimeSegments (by decide : 35258413 ≤ 35323949)
    (by decide : 35323949 ≤ 35389485) join_0_0 join_0_1

theorem total : (twinPrimeSegment 35258413 35389485).card = 566 := join_1_0

end S016C13
end Sude.GeneratedTwinScan
