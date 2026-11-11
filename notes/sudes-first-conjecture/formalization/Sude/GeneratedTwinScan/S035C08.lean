import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S035C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 74448941 74481709 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 74448941 74481709).card = 111 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 74448941 74481709
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 74481709 74514477 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 74481709 74514477).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 74481709 74514477
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 74514477 74547245 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 74514477 74547245).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 74514477 74547245
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 74547245 74580013 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 74547245 74580013).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 74547245 74580013
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 74448941 74514477).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 74448941 ≤ 74481709)
    (by decide : 74481709 ≤ 74514477) block0 block1

theorem join_0_1 : (twinPrimeSegment 74514477 74580013).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 74514477 ≤ 74547245)
    (by decide : 74547245 ≤ 74580013) block2 block3

theorem join_1_0 : (twinPrimeSegment 74448941 74580013).card = 480 := by
  simpa using combineTwinPrimeSegments (by decide : 74448941 ≤ 74514477)
    (by decide : 74514477 ≤ 74580013) join_0_0 join_0_1

theorem total : (twinPrimeSegment 74448941 74580013).card = 480 := join_1_0

end S035C08
end Sude.GeneratedTwinScan
