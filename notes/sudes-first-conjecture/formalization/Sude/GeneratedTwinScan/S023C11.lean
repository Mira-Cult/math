import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S023C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 49676333 widths0 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 49676333 49709101).card = 134 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 49676333 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 49709101 widths1 = 145 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 49709101 49741869).card = 145 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 49709101 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 49741869 widths2 = 144 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 49741869 49774637).card = 144 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 49741869 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 49774637 widths3 = 139 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 49774637 49807405).card = 139 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 49774637 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 49676333 49741869).card = 279 := by
  simpa using combineTwinPrimeSegments (by decide : 49676333 ≤ 49709101)
    (by decide : 49709101 ≤ 49741869) block0 block1

theorem join_0_1 : (twinPrimeSegment 49741869 49807405).card = 283 := by
  simpa using combineTwinPrimeSegments (by decide : 49741869 ≤ 49774637)
    (by decide : 49774637 ≤ 49807405) block2 block3

theorem join_1_0 : (twinPrimeSegment 49676333 49807405).card = 562 := by
  simpa using combineTwinPrimeSegments (by decide : 49676333 ≤ 49741869)
    (by decide : 49741869 ≤ 49807405) join_0_0 join_0_1

theorem total : (twinPrimeSegment 49676333 49807405).card = 562 := join_1_0

end S023C11
end Sude.GeneratedTwinScan
