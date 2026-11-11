import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S025C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 53608493 widths0 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 53608493 53641261).card = 135 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 53608493 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 53641261 widths1 = 145 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 53641261 53674029).card = 145 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 53641261 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 53674029 widths2 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 53674029 53706797).card = 122 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 53674029 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 53706797 widths3 = 151 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 53706797 53739565).card = 151 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 53706797 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 53608493 53674029).card = 280 := by
  simpa using combineTwinPrimeSegments (by decide : 53608493 ≤ 53641261)
    (by decide : 53641261 ≤ 53674029) block0 block1

theorem join_0_1 : (twinPrimeSegment 53674029 53739565).card = 273 := by
  simpa using combineTwinPrimeSegments (by decide : 53674029 ≤ 53706797)
    (by decide : 53706797 ≤ 53739565) block2 block3

theorem join_1_0 : (twinPrimeSegment 53608493 53739565).card = 553 := by
  simpa using combineTwinPrimeSegments (by decide : 53608493 ≤ 53674029)
    (by decide : 53674029 ≤ 53739565) join_0_0 join_0_1

theorem total : (twinPrimeSegment 53608493 53739565).card = 553 := join_1_0

end S025C09
end Sude.GeneratedTwinScan
