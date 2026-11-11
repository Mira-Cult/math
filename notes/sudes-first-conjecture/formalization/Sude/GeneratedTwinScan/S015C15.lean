import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S015C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 33423405 widths0 = 155 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 33423405 33456173).card = 155 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 33423405 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 33456173 widths1 = 158 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 33456173 33488941).card = 158 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 33456173 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 33488941 widths2 = 149 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 33488941 33521709).card = 149 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 33488941 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 33521709 widths3 = 141 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 33521709 33554477).card = 141 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 33521709 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 33423405 33488941).card = 313 := by
  simpa using combineTwinPrimeSegments (by decide : 33423405 ≤ 33456173)
    (by decide : 33456173 ≤ 33488941) block0 block1

theorem join_0_1 : (twinPrimeSegment 33488941 33554477).card = 290 := by
  simpa using combineTwinPrimeSegments (by decide : 33488941 ≤ 33521709)
    (by decide : 33521709 ≤ 33554477) block2 block3

theorem join_1_0 : (twinPrimeSegment 33423405 33554477).card = 603 := by
  simpa using combineTwinPrimeSegments (by decide : 33423405 ≤ 33488941)
    (by decide : 33488941 ≤ 33554477) join_0_0 join_0_1

theorem total : (twinPrimeSegment 33423405 33554477).card = 603 := join_1_0

end S015C15
end Sude.GeneratedTwinScan
