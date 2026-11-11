import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S022C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 47841325 widths0 = 141 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 47841325 47874093).card = 141 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 47841325 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 47874093 widths1 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 47874093 47906861).card = 135 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 47874093 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 47906861 widths2 = 146 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 47906861 47939629).card = 146 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 47906861 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 47939629 widths3 = 159 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 47939629 47972397).card = 159 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 47939629 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 47841325 47906861).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 47841325 ≤ 47874093)
    (by decide : 47874093 ≤ 47906861) block0 block1

theorem join_0_1 : (twinPrimeSegment 47906861 47972397).card = 305 := by
  simpa using combineTwinPrimeSegments (by decide : 47906861 ≤ 47939629)
    (by decide : 47939629 ≤ 47972397) block2 block3

theorem join_1_0 : (twinPrimeSegment 47841325 47972397).card = 581 := by
  simpa using combineTwinPrimeSegments (by decide : 47841325 ≤ 47906861)
    (by decide : 47906861 ≤ 47972397) join_0_0 join_0_1

theorem total : (twinPrimeSegment 47841325 47972397).card = 581 := join_1_0

end S022C13
end Sude.GeneratedTwinScan
