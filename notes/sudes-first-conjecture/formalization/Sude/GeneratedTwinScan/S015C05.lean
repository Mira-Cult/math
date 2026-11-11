import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S015C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 32112685 widths0 = 154 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 32112685 32145453).card = 154 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 32112685 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 32145453 widths1 = 146 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 32145453 32178221).card = 146 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 32145453 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 32178221 widths2 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 32178221 32210989).card = 129 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 32178221 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 32210989 widths3 = 143 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 32210989 32243757).card = 143 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 32210989 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 32112685 32178221).card = 300 := by
  simpa using combineTwinPrimeSegments (by decide : 32112685 ≤ 32145453)
    (by decide : 32145453 ≤ 32178221) block0 block1

theorem join_0_1 : (twinPrimeSegment 32178221 32243757).card = 272 := by
  simpa using combineTwinPrimeSegments (by decide : 32178221 ≤ 32210989)
    (by decide : 32210989 ≤ 32243757) block2 block3

theorem join_1_0 : (twinPrimeSegment 32112685 32243757).card = 572 := by
  simpa using combineTwinPrimeSegments (by decide : 32112685 ≤ 32178221)
    (by decide : 32178221 ≤ 32243757) join_0_0 join_0_1

theorem total : (twinPrimeSegment 32112685 32243757).card = 572 := join_1_0

end S015C05
end Sude.GeneratedTwinScan
