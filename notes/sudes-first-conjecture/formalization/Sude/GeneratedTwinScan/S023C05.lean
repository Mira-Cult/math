import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S023C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 48889901 widths0 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 48889901 48922669).card = 116 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 48889901 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 48922669 widths1 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 48922669 48955437).card = 132 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 48922669 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 48955437 widths2 = 145 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 48955437 48988205).card = 145 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 48955437 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 48988205 widths3 = 140 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 48988205 49020973).card = 140 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 48988205 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 48889901 48955437).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 48889901 ≤ 48922669)
    (by decide : 48922669 ≤ 48955437) block0 block1

theorem join_0_1 : (twinPrimeSegment 48955437 49020973).card = 285 := by
  simpa using combineTwinPrimeSegments (by decide : 48955437 ≤ 48988205)
    (by decide : 48988205 ≤ 49020973) block2 block3

theorem join_1_0 : (twinPrimeSegment 48889901 49020973).card = 533 := by
  simpa using combineTwinPrimeSegments (by decide : 48889901 ≤ 48955437)
    (by decide : 48955437 ≤ 49020973) join_0_0 join_0_1

theorem total : (twinPrimeSegment 48889901 49020973).card = 533 := join_1_0

end S023C05
end Sude.GeneratedTwinScan
