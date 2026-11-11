import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S020C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 43515949 widths0 = 154 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 43515949 43548717).card = 154 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 43515949 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 43548717 widths1 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 43548717 43581485).card = 129 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 43548717 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 43581485 widths2 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 43581485 43614253).card = 126 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 43581485 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 43614253 widths3 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 43614253 43647021).card = 125 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 43614253 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 43515949 43581485).card = 283 := by
  simpa using combineTwinPrimeSegments (by decide : 43515949 ≤ 43548717)
    (by decide : 43548717 ≤ 43581485) block0 block1

theorem join_0_1 : (twinPrimeSegment 43581485 43647021).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 43581485 ≤ 43614253)
    (by decide : 43614253 ≤ 43647021) block2 block3

theorem join_1_0 : (twinPrimeSegment 43515949 43647021).card = 534 := by
  simpa using combineTwinPrimeSegments (by decide : 43515949 ≤ 43581485)
    (by decide : 43581485 ≤ 43647021) join_0_0 join_0_1

theorem total : (twinPrimeSegment 43515949 43647021).card = 534 := join_1_0

end S020C12
end Sude.GeneratedTwinScan
