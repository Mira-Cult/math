import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S019C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 39977005 widths0 = 156 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 39977005 40009773).card = 156 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 39977005 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 40009773 widths1 = 151 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 40009773 40042541).card = 151 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 40009773 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 40042541 widths2 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 40042541 40075309).card = 132 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 40042541 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 40075309 widths3 = 148 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 40075309 40108077).card = 148 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 40075309 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 39977005 40042541).card = 307 := by
  simpa using combineTwinPrimeSegments (by decide : 39977005 ≤ 40009773)
    (by decide : 40009773 ≤ 40042541) block0 block1

theorem join_0_1 : (twinPrimeSegment 40042541 40108077).card = 280 := by
  simpa using combineTwinPrimeSegments (by decide : 40042541 ≤ 40075309)
    (by decide : 40075309 ≤ 40108077) block2 block3

theorem join_1_0 : (twinPrimeSegment 39977005 40108077).card = 587 := by
  simpa using combineTwinPrimeSegments (by decide : 39977005 ≤ 40042541)
    (by decide : 40042541 ≤ 40108077) join_0_0 join_0_1

theorem total : (twinPrimeSegment 39977005 40108077).card = 587 := join_1_0

end S019C01
end Sude.GeneratedTwinScan
