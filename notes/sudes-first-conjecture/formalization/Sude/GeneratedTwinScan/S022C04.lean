import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S022C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 46661677 widths0 = 145 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 46661677 46694445).card = 145 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 46661677 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 46694445 widths1 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 46694445 46727213).card = 129 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 46694445 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 46727213 widths2 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 46727213 46759981).card = 120 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 46727213 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 46759981 widths3 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 46759981 46792749).card = 131 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 46759981 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 46661677 46727213).card = 274 := by
  simpa using combineTwinPrimeSegments (by decide : 46661677 ≤ 46694445)
    (by decide : 46694445 ≤ 46727213) block0 block1

theorem join_0_1 : (twinPrimeSegment 46727213 46792749).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 46727213 ≤ 46759981)
    (by decide : 46759981 ≤ 46792749) block2 block3

theorem join_1_0 : (twinPrimeSegment 46661677 46792749).card = 525 := by
  simpa using combineTwinPrimeSegments (by decide : 46661677 ≤ 46727213)
    (by decide : 46727213 ≤ 46792749) join_0_0 join_0_1

theorem total : (twinPrimeSegment 46661677 46792749).card = 525 := join_1_0

end S022C04
end Sude.GeneratedTwinScan
