import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S020C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 42598445 widths0 = 142 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 42598445 42631213).card = 142 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 42598445 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 42631213 widths1 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 42631213 42663981).card = 132 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 42631213 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 42663981 widths2 = 141 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 42663981 42696749).card = 141 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 42663981 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 42696749 widths3 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 42696749 42729517).card = 137 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 42696749 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 42598445 42663981).card = 274 := by
  simpa using combineTwinPrimeSegments (by decide : 42598445 ≤ 42631213)
    (by decide : 42631213 ≤ 42663981) block0 block1

theorem join_0_1 : (twinPrimeSegment 42663981 42729517).card = 278 := by
  simpa using combineTwinPrimeSegments (by decide : 42663981 ≤ 42696749)
    (by decide : 42696749 ≤ 42729517) block2 block3

theorem join_1_0 : (twinPrimeSegment 42598445 42729517).card = 552 := by
  simpa using combineTwinPrimeSegments (by decide : 42598445 ≤ 42663981)
    (by decide : 42663981 ≤ 42729517) join_0_0 join_0_1

theorem total : (twinPrimeSegment 42598445 42729517).card = 552 := join_1_0

end S020C05
end Sude.GeneratedTwinScan
