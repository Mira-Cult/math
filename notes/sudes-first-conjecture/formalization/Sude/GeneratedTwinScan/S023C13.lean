import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S023C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 49938477 widths0 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 49938477 49971245).card = 132 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 49938477 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 49971245 widths1 = 156 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 49971245 50004013).card = 156 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 49971245 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 50004013 widths2 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 50004013 50036781).card = 137 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 50004013 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 50036781 widths3 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 50036781 50069549).card = 129 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 50036781 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 49938477 50004013).card = 288 := by
  simpa using combineTwinPrimeSegments (by decide : 49938477 ≤ 49971245)
    (by decide : 49971245 ≤ 50004013) block0 block1

theorem join_0_1 : (twinPrimeSegment 50004013 50069549).card = 266 := by
  simpa using combineTwinPrimeSegments (by decide : 50004013 ≤ 50036781)
    (by decide : 50036781 ≤ 50069549) block2 block3

theorem join_1_0 : (twinPrimeSegment 49938477 50069549).card = 554 := by
  simpa using combineTwinPrimeSegments (by decide : 49938477 ≤ 50004013)
    (by decide : 50004013 ≤ 50069549) join_0_0 join_0_1

theorem total : (twinPrimeSegment 49938477 50069549).card = 554 := join_1_0

end S023C13
end Sude.GeneratedTwinScan
