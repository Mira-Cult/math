import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S034C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 71303213 71335981 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 71303213 71335981).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 71303213 71335981
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 71335981 71368749 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 71335981 71368749).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 71335981 71368749
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 71368749 71401517 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 71368749 71401517).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 71368749 71401517
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 71401517 71434285 = 145 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 71401517 71434285).card = 145 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 71401517 71434285
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 71303213 71368749).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 71303213 ≤ 71335981)
    (by decide : 71335981 ≤ 71368749) block0 block1

theorem join_0_1 : (twinPrimeSegment 71368749 71434285).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 71368749 ≤ 71401517)
    (by decide : 71401517 ≤ 71434285) block2 block3

theorem join_1_0 : (twinPrimeSegment 71303213 71434285).card = 520 := by
  simpa using combineTwinPrimeSegments (by decide : 71303213 ≤ 71368749)
    (by decide : 71368749 ≤ 71434285) join_0_0 join_0_1

theorem total : (twinPrimeSegment 71303213 71434285).card = 520 := join_1_0

end S034C00
end Sude.GeneratedTwinScan
