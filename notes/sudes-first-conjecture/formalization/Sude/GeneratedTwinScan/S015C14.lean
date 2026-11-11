import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S015C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 33292333 widths0 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 33292333 33325101).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 33292333 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 33325101 widths1 = 144 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 33325101 33357869).card = 144 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 33325101 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 33357869 widths2 = 153 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 33357869 33390637).card = 153 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 33357869 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 33390637 widths3 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 33390637 33423405).card = 129 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 33390637 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 33292333 33357869).card = 282 := by
  simpa using combineTwinPrimeSegments (by decide : 33292333 ≤ 33325101)
    (by decide : 33325101 ≤ 33357869) block0 block1

theorem join_0_1 : (twinPrimeSegment 33357869 33423405).card = 282 := by
  simpa using combineTwinPrimeSegments (by decide : 33357869 ≤ 33390637)
    (by decide : 33390637 ≤ 33423405) block2 block3

theorem join_1_0 : (twinPrimeSegment 33292333 33423405).card = 564 := by
  simpa using combineTwinPrimeSegments (by decide : 33292333 ≤ 33357869)
    (by decide : 33357869 ≤ 33423405) join_0_0 join_0_1

theorem total : (twinPrimeSegment 33292333 33423405).card = 564 := join_1_0

end S015C14
end Sude.GeneratedTwinScan
