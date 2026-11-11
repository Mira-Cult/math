import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S016C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 34340909 widths0 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 34340909 34373677).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 34340909 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 34373677 widths1 = 147 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 34373677 34406445).card = 147 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 34373677 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 34406445 widths2 = 140 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 34406445 34439213).card = 140 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 34406445 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 34439213 widths3 = 151 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 34439213 34471981).card = 151 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 34439213 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 34340909 34406445).card = 285 := by
  simpa using combineTwinPrimeSegments (by decide : 34340909 ≤ 34373677)
    (by decide : 34373677 ≤ 34406445) block0 block1

theorem join_0_1 : (twinPrimeSegment 34406445 34471981).card = 291 := by
  simpa using combineTwinPrimeSegments (by decide : 34406445 ≤ 34439213)
    (by decide : 34439213 ≤ 34471981) block2 block3

theorem join_1_0 : (twinPrimeSegment 34340909 34471981).card = 576 := by
  simpa using combineTwinPrimeSegments (by decide : 34340909 ≤ 34406445)
    (by decide : 34406445 ≤ 34471981) join_0_0 join_0_1

theorem total : (twinPrimeSegment 34340909 34471981).card = 576 := join_1_0

end S016C06
end Sude.GeneratedTwinScan
