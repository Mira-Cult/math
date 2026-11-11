import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S071C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 149028909 149061677 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 149028909 149061677).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 149028909 149061677
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 149061677 149094445 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 149061677 149094445).card = 98 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 149061677 149094445
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 149094445 149127213 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 149094445 149127213).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 149094445 149127213
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 149127213 149159981 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 149127213 149159981).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 149127213 149159981
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 149028909 149094445).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 149028909 ≤ 149061677)
    (by decide : 149061677 ≤ 149094445) block0 block1

theorem join_0_1 : (twinPrimeSegment 149094445 149159981).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 149094445 ≤ 149127213)
    (by decide : 149127213 ≤ 149159981) block2 block3

theorem join_1_0 : (twinPrimeSegment 149028909 149159981).card = 486 := by
  simpa using combineTwinPrimeSegments (by decide : 149028909 ≤ 149094445)
    (by decide : 149094445 ≤ 149159981) join_0_0 join_0_1

theorem total : (twinPrimeSegment 149028909 149159981).card = 486 := join_1_0

end S071C01
end Sude.GeneratedTwinScan
