import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S017C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 37486637 widths0 = 154 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 37486637 37519405).card = 154 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 37486637 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 37519405 widths1 = 141 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 37519405 37552173).card = 141 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 37519405 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 37552173 widths2 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 37552173 37584941).card = 132 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 37552173 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 37584941 widths3 = 148 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 37584941 37617709).card = 148 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 37584941 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 37486637 37552173).card = 295 := by
  simpa using combineTwinPrimeSegments (by decide : 37486637 ≤ 37519405)
    (by decide : 37519405 ≤ 37552173) block0 block1

theorem join_0_1 : (twinPrimeSegment 37552173 37617709).card = 280 := by
  simpa using combineTwinPrimeSegments (by decide : 37552173 ≤ 37584941)
    (by decide : 37584941 ≤ 37617709) block2 block3

theorem join_1_0 : (twinPrimeSegment 37486637 37617709).card = 575 := by
  simpa using combineTwinPrimeSegments (by decide : 37486637 ≤ 37552173)
    (by decide : 37552173 ≤ 37617709) join_0_0 join_0_1

theorem total : (twinPrimeSegment 37486637 37617709).card = 575 := join_1_0

end S017C14
end Sude.GeneratedTwinScan
