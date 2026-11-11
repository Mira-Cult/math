import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S017C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 36044845 widths0 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 36044845 36077613).card = 132 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 36044845 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 36077613 widths1 = 160 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 36077613 36110381).card = 160 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 36077613 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 36110381 widths2 = 141 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 36110381 36143149).card = 141 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 36110381 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 36143149 widths3 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 36143149 36175917).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 36143149 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 36044845 36110381).card = 292 := by
  simpa using combineTwinPrimeSegments (by decide : 36044845 ≤ 36077613)
    (by decide : 36077613 ≤ 36110381) block0 block1

theorem join_0_1 : (twinPrimeSegment 36110381 36175917).card = 279 := by
  simpa using combineTwinPrimeSegments (by decide : 36110381 ≤ 36143149)
    (by decide : 36143149 ≤ 36175917) block2 block3

theorem join_1_0 : (twinPrimeSegment 36044845 36175917).card = 571 := by
  simpa using combineTwinPrimeSegments (by decide : 36044845 ≤ 36110381)
    (by decide : 36110381 ≤ 36175917) join_0_0 join_0_1

theorem total : (twinPrimeSegment 36044845 36175917).card = 571 := join_1_0

end S017C03
end Sude.GeneratedTwinScan
