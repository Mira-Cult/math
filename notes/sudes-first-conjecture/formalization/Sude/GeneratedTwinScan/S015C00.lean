import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S015C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 31457325 widths0 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 31457325 31490093).card = 134 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 31457325 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 31490093 widths1 = 153 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 31490093 31522861).card = 153 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 31490093 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 31522861 widths2 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 31522861 31555629).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 31522861 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 31555629 widths3 = 148 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 31555629 31588397).card = 148 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 31555629 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 31457325 31522861).card = 287 := by
  simpa using combineTwinPrimeSegments (by decide : 31457325 ≤ 31490093)
    (by decide : 31490093 ≤ 31522861) block0 block1

theorem join_0_1 : (twinPrimeSegment 31522861 31588397).card = 286 := by
  simpa using combineTwinPrimeSegments (by decide : 31522861 ≤ 31555629)
    (by decide : 31555629 ≤ 31588397) block2 block3

theorem join_1_0 : (twinPrimeSegment 31457325 31588397).card = 573 := by
  simpa using combineTwinPrimeSegments (by decide : 31457325 ≤ 31522861)
    (by decide : 31522861 ≤ 31588397) join_0_0 join_0_1

theorem total : (twinPrimeSegment 31457325 31588397).card = 573 := join_1_0

end S015C00
end Sude.GeneratedTwinScan
