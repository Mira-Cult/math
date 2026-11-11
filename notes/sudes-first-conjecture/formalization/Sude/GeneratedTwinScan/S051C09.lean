import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S051C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 108134445 108167213 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 108134445 108167213).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 108134445 108167213
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 108167213 108199981 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 108167213 108199981).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 108167213 108199981
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 108199981 108232749 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 108199981 108232749).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 108199981 108232749
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 108232749 108265517 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 108232749 108265517).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 108232749 108265517
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 108134445 108199981).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 108134445 ≤ 108167213)
    (by decide : 108167213 ≤ 108199981) block0 block1

theorem join_0_1 : (twinPrimeSegment 108199981 108265517).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 108199981 ≤ 108232749)
    (by decide : 108232749 ≤ 108265517) block2 block3

theorem join_1_0 : (twinPrimeSegment 108134445 108265517).card = 501 := by
  simpa using combineTwinPrimeSegments (by decide : 108134445 ≤ 108199981)
    (by decide : 108199981 ≤ 108265517) join_0_0 join_0_1

theorem total : (twinPrimeSegment 108134445 108265517).card = 501 := join_1_0

end S051C09
end Sude.GeneratedTwinScan
