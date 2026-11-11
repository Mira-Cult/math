import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S017C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 35913773 widths0 = 140 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 35913773 35946541).card = 140 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 35913773 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 35946541 widths1 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 35946541 35979309).card = 125 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 35946541 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 35979309 widths2 = 157 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 35979309 36012077).card = 157 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 35979309 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 36012077 widths3 = 149 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 36012077 36044845).card = 149 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 36012077 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 35913773 35979309).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 35913773 ≤ 35946541)
    (by decide : 35946541 ≤ 35979309) block0 block1

theorem join_0_1 : (twinPrimeSegment 35979309 36044845).card = 306 := by
  simpa using combineTwinPrimeSegments (by decide : 35979309 ≤ 36012077)
    (by decide : 36012077 ≤ 36044845) block2 block3

theorem join_1_0 : (twinPrimeSegment 35913773 36044845).card = 571 := by
  simpa using combineTwinPrimeSegments (by decide : 35913773 ≤ 35979309)
    (by decide : 35979309 ≤ 36044845) join_0_0 join_0_1

theorem total : (twinPrimeSegment 35913773 36044845).card = 571 := join_1_0

end S017C02
end Sude.GeneratedTwinScan
