import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S021C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 45482029 widths0 = 143 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 45482029 45514797).card = 143 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 45482029 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 45514797 widths1 = 150 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 45514797 45547565).card = 150 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 45514797 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 45547565 widths2 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 45547565 45580333).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 45547565 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 45580333 widths3 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 45580333 45613101).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 45580333 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 45482029 45547565).card = 293 := by
  simpa using combineTwinPrimeSegments (by decide : 45482029 ≤ 45514797)
    (by decide : 45514797 ≤ 45547565) block0 block1

theorem join_0_1 : (twinPrimeSegment 45547565 45613101).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 45547565 ≤ 45580333)
    (by decide : 45580333 ≤ 45613101) block2 block3

theorem join_1_0 : (twinPrimeSegment 45482029 45613101).card = 569 := by
  simpa using combineTwinPrimeSegments (by decide : 45482029 ≤ 45547565)
    (by decide : 45547565 ≤ 45613101) join_0_0 join_0_1

theorem total : (twinPrimeSegment 45482029 45613101).card = 569 := join_1_0

end S021C11
end Sude.GeneratedTwinScan
