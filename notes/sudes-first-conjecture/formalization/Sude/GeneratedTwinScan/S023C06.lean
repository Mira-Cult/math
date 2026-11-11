import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S023C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 49020973 widths0 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 49020973 49053741).card = 131 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 49020973 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 49053741 widths1 = 161 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 49053741 49086509).card = 161 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 49053741 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 49086509 widths2 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 49086509 49119277).card = 118 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 49086509 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 49119277 widths3 = 147 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 49119277 49152045).card = 147 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 49119277 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 49020973 49086509).card = 292 := by
  simpa using combineTwinPrimeSegments (by decide : 49020973 ≤ 49053741)
    (by decide : 49053741 ≤ 49086509) block0 block1

theorem join_0_1 : (twinPrimeSegment 49086509 49152045).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 49086509 ≤ 49119277)
    (by decide : 49119277 ≤ 49152045) block2 block3

theorem join_1_0 : (twinPrimeSegment 49020973 49152045).card = 557 := by
  simpa using combineTwinPrimeSegments (by decide : 49020973 ≤ 49086509)
    (by decide : 49086509 ≤ 49152045) join_0_0 join_0_1

theorem total : (twinPrimeSegment 49020973 49152045).card = 557 := join_1_0

end S023C06
end Sude.GeneratedTwinScan
