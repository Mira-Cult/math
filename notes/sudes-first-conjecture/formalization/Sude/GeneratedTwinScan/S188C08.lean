import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S188C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19883)) 395313197 395345965 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 395313197 395345965).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19883 395313197 395345965
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19884)) 395345965 395378733 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 395345965 395378733).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19884 395345965 395378733
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19884)) 395378733 395411501 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 395378733 395411501).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19884 395378733 395411501
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19885)) 395411501 395444269 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 395411501 395444269).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19885 395411501 395444269
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 395313197 395378733).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 395313197 ≤ 395345965)
    (by decide : 395345965 ≤ 395378733) block0 block1

theorem join_0_1 : (twinPrimeSegment 395378733 395444269).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 395378733 ≤ 395411501)
    (by decide : 395411501 ≤ 395444269) block2 block3

theorem join_1_0 : (twinPrimeSegment 395313197 395444269).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 395313197 ≤ 395378733)
    (by decide : 395378733 ≤ 395444269) join_0_0 join_0_1

theorem total : (twinPrimeSegment 395313197 395444269).card = 436 := join_1_0

end S188C08
end Sude.GeneratedTwinScan
