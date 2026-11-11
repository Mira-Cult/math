import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S016C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 34471981 widths0 = 140 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 34471981 34504749).card = 140 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 34471981 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 34504749 widths1 = 141 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 34504749 34537517).card = 141 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 34504749 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 34537517 widths2 = 149 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 34537517 34570285).card = 149 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 34537517 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 34570285 widths3 = 160 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 34570285 34603053).card = 160 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 34570285 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 34471981 34537517).card = 281 := by
  simpa using combineTwinPrimeSegments (by decide : 34471981 ≤ 34504749)
    (by decide : 34504749 ≤ 34537517) block0 block1

theorem join_0_1 : (twinPrimeSegment 34537517 34603053).card = 309 := by
  simpa using combineTwinPrimeSegments (by decide : 34537517 ≤ 34570285)
    (by decide : 34570285 ≤ 34603053) block2 block3

theorem join_1_0 : (twinPrimeSegment 34471981 34603053).card = 590 := by
  simpa using combineTwinPrimeSegments (by decide : 34471981 ≤ 34537517)
    (by decide : 34537517 ≤ 34603053) join_0_0 join_0_1

theorem total : (twinPrimeSegment 34471981 34603053).card = 590 := join_1_0

end S016C07
end Sude.GeneratedTwinScan
