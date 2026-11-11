import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S018C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 39714861 widths0 = 147 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 39714861 39747629).card = 147 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 39714861 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 39747629 widths1 = 146 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 39747629 39780397).card = 146 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 39747629 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 39780397 widths2 = 149 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 39780397 39813165).card = 149 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 39780397 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 39813165 widths3 = 150 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 39813165 39845933).card = 150 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 39813165 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 39714861 39780397).card = 293 := by
  simpa using combineTwinPrimeSegments (by decide : 39714861 ≤ 39747629)
    (by decide : 39747629 ≤ 39780397) block0 block1

theorem join_0_1 : (twinPrimeSegment 39780397 39845933).card = 299 := by
  simpa using combineTwinPrimeSegments (by decide : 39780397 ≤ 39813165)
    (by decide : 39813165 ≤ 39845933) block2 block3

theorem join_1_0 : (twinPrimeSegment 39714861 39845933).card = 592 := by
  simpa using combineTwinPrimeSegments (by decide : 39714861 ≤ 39780397)
    (by decide : 39780397 ≤ 39845933) join_0_0 join_0_1

theorem total : (twinPrimeSegment 39714861 39845933).card = 592 := join_1_0

end S018C15
end Sude.GeneratedTwinScan
