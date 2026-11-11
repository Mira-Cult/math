import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S020C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 42991661 widths0 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 42991661 43024429).card = 125 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 42991661 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 43024429 widths1 = 147 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 43024429 43057197).card = 147 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 43024429 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 43057197 widths2 = 169 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 43057197 43089965).card = 169 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 43057197 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 43089965 widths3 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 43089965 43122733).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 43089965 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 42991661 43057197).card = 272 := by
  simpa using combineTwinPrimeSegments (by decide : 42991661 ≤ 43024429)
    (by decide : 43024429 ≤ 43057197) block0 block1

theorem join_0_1 : (twinPrimeSegment 43057197 43122733).card = 307 := by
  simpa using combineTwinPrimeSegments (by decide : 43057197 ≤ 43089965)
    (by decide : 43089965 ≤ 43122733) block2 block3

theorem join_1_0 : (twinPrimeSegment 42991661 43122733).card = 579 := by
  simpa using combineTwinPrimeSegments (by decide : 42991661 ≤ 43057197)
    (by decide : 43057197 ≤ 43122733) join_0_0 join_0_1

theorem total : (twinPrimeSegment 42991661 43122733).card = 579 := join_1_0

end S020C08
end Sude.GeneratedTwinScan
