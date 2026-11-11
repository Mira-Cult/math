import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S016C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 35127341 widths0 = 148 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 35127341 35160109).card = 148 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 35127341 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 35160109 widths1 = 136 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 35160109 35192877).card = 136 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 35160109 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 35192877 widths2 = 144 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 35192877 35225645).card = 144 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 35192877 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 35225645 widths3 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 35225645 35258413).card = 137 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 35225645 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 35127341 35192877).card = 284 := by
  simpa using combineTwinPrimeSegments (by decide : 35127341 ≤ 35160109)
    (by decide : 35160109 ≤ 35192877) block0 block1

theorem join_0_1 : (twinPrimeSegment 35192877 35258413).card = 281 := by
  simpa using combineTwinPrimeSegments (by decide : 35192877 ≤ 35225645)
    (by decide : 35225645 ≤ 35258413) block2 block3

theorem join_1_0 : (twinPrimeSegment 35127341 35258413).card = 565 := by
  simpa using combineTwinPrimeSegments (by decide : 35127341 ≤ 35192877)
    (by decide : 35192877 ≤ 35258413) join_0_0 join_0_1

theorem total : (twinPrimeSegment 35127341 35258413).card = 565 := join_1_0

end S016C12
end Sude.GeneratedTwinScan
