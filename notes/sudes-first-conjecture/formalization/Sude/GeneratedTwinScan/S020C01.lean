import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S020C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 42074157 widths0 = 140 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 42074157 42106925).card = 140 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 42074157 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 42106925 widths1 = 141 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 42106925 42139693).card = 141 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 42106925 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 42139693 widths2 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 42139693 42172461).card = 128 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 42139693 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 42172461 widths3 = 152 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 42172461 42205229).card = 152 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 42172461 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 42074157 42139693).card = 281 := by
  simpa using combineTwinPrimeSegments (by decide : 42074157 ≤ 42106925)
    (by decide : 42106925 ≤ 42139693) block0 block1

theorem join_0_1 : (twinPrimeSegment 42139693 42205229).card = 280 := by
  simpa using combineTwinPrimeSegments (by decide : 42139693 ≤ 42172461)
    (by decide : 42172461 ≤ 42205229) block2 block3

theorem join_1_0 : (twinPrimeSegment 42074157 42205229).card = 561 := by
  simpa using combineTwinPrimeSegments (by decide : 42074157 ≤ 42139693)
    (by decide : 42139693 ≤ 42205229) join_0_0 join_0_1

theorem total : (twinPrimeSegment 42074157 42205229).card = 561 := join_1_0

end S020C01
end Sude.GeneratedTwinScan
