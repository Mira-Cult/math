import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S070C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 148111405 148144173 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 148111405 148144173).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 148111405 148144173
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 148144173 148176941 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 148144173 148176941).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 148144173 148176941
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 148176941 148209709 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 148176941 148209709).card = 108 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 148176941 148209709
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 148209709 148242477 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 148209709 148242477).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 148209709 148242477
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 148111405 148176941).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 148111405 ≤ 148144173)
    (by decide : 148144173 ≤ 148176941) block0 block1

theorem join_0_1 : (twinPrimeSegment 148176941 148242477).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 148176941 ≤ 148209709)
    (by decide : 148209709 ≤ 148242477) block2 block3

theorem join_1_0 : (twinPrimeSegment 148111405 148242477).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 148111405 ≤ 148176941)
    (by decide : 148176941 ≤ 148242477) join_0_0 join_0_1

theorem total : (twinPrimeSegment 148111405 148242477).card = 461 := join_1_0

end S070C10
end Sude.GeneratedTwinScan
