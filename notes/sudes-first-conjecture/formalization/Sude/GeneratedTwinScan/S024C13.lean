import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S024C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 52035629 widths0 = 160 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 52035629 52068397).card = 160 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 52035629 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 52068397 widths1 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 52068397 52101165).card = 135 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 52068397 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 52101165 widths2 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 52101165 52133933).card = 131 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 52101165 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 52133933 widths3 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 52133933 52166701).card = 132 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 52133933 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 52035629 52101165).card = 295 := by
  simpa using combineTwinPrimeSegments (by decide : 52035629 ≤ 52068397)
    (by decide : 52068397 ≤ 52101165) block0 block1

theorem join_0_1 : (twinPrimeSegment 52101165 52166701).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 52101165 ≤ 52133933)
    (by decide : 52133933 ≤ 52166701) block2 block3

theorem join_1_0 : (twinPrimeSegment 52035629 52166701).card = 558 := by
  simpa using combineTwinPrimeSegments (by decide : 52035629 ≤ 52101165)
    (by decide : 52101165 ≤ 52166701) join_0_0 join_0_1

theorem total : (twinPrimeSegment 52035629 52166701).card = 558 := join_1_0

end S024C13
end Sude.GeneratedTwinScan
