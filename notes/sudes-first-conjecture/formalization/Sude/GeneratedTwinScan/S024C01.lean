import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S024C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 50462765 widths0 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 50462765 50495533).card = 122 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 50462765 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 50495533 widths1 = 146 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 50495533 50528301).card = 146 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 50495533 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 50528301 widths2 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 50528301 50561069).card = 115 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 50528301 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 50561069 widths3 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 50561069 50593837).card = 136 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 50561069 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 50462765 50528301).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 50462765 ≤ 50495533)
    (by decide : 50495533 ≤ 50528301) block0 block1

theorem join_0_1 : (twinPrimeSegment 50528301 50593837).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 50528301 ≤ 50561069)
    (by decide : 50561069 ≤ 50593837) block2 block3

theorem join_1_0 : (twinPrimeSegment 50462765 50593837).card = 519 := by
  simpa using combineTwinPrimeSegments (by decide : 50462765 ≤ 50528301)
    (by decide : 50528301 ≤ 50593837) join_0_0 join_0_1

theorem total : (twinPrimeSegment 50462765 50593837).card = 519 := join_1_0

end S024C01
end Sude.GeneratedTwinScan
