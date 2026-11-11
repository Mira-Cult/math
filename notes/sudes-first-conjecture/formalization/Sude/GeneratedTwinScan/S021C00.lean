import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S021C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 44040237 widths0 = 143 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 44040237 44073005).card = 143 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 44040237 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 44073005 widths1 = 137 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 44073005 44105773).card = 137 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 44073005 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 44105773 widths2 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 44105773 44138541).card = 130 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 44105773 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 44138541 widths3 = 147 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 44138541 44171309).card = 147 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 44138541 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 44040237 44105773).card = 280 := by
  simpa using combineTwinPrimeSegments (by decide : 44040237 ≤ 44073005)
    (by decide : 44073005 ≤ 44105773) block0 block1

theorem join_0_1 : (twinPrimeSegment 44105773 44171309).card = 277 := by
  simpa using combineTwinPrimeSegments (by decide : 44105773 ≤ 44138541)
    (by decide : 44138541 ≤ 44171309) block2 block3

theorem join_1_0 : (twinPrimeSegment 44040237 44171309).card = 557 := by
  simpa using combineTwinPrimeSegments (by decide : 44040237 ≤ 44105773)
    (by decide : 44105773 ≤ 44171309) join_0_0 join_0_1

theorem total : (twinPrimeSegment 44040237 44171309).card = 557 := join_1_0

end S021C00
end Sude.GeneratedTwinScan
