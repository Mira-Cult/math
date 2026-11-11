import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S016C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 35520557 widths0 = 140 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 35520557 35553325).card = 140 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 35520557 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 35553325 widths1 = 142 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 35553325 35586093).card = 142 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 35553325 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 35586093 widths2 = 172 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 35586093 35618861).card = 172 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 35586093 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 35618861 widths3 = 152 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 35618861 35651629).card = 152 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 35618861 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 35520557 35586093).card = 282 := by
  simpa using combineTwinPrimeSegments (by decide : 35520557 ≤ 35553325)
    (by decide : 35553325 ≤ 35586093) block0 block1

theorem join_0_1 : (twinPrimeSegment 35586093 35651629).card = 324 := by
  simpa using combineTwinPrimeSegments (by decide : 35586093 ≤ 35618861)
    (by decide : 35618861 ≤ 35651629) block2 block3

theorem join_1_0 : (twinPrimeSegment 35520557 35651629).card = 606 := by
  simpa using combineTwinPrimeSegments (by decide : 35520557 ≤ 35586093)
    (by decide : 35586093 ≤ 35651629) join_0_0 join_0_1

theorem total : (twinPrimeSegment 35520557 35651629).card = 606 := join_1_0

end S016C15
end Sude.GeneratedTwinScan
