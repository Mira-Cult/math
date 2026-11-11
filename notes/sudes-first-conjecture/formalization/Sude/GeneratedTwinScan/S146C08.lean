import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S146C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17528)) 307232813 307265581 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 307232813 307265581).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17528 307232813 307265581
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17529)) 307265581 307298349 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 307265581 307298349).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17529 307265581 307298349
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17530)) 307298349 307331117 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 307298349 307331117).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17530 307298349 307331117
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17531)) 307331117 307363885 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 307331117 307363885).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17531 307331117 307363885
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 307232813 307298349).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 307232813 ≤ 307265581)
    (by decide : 307265581 ≤ 307298349) block0 block1

theorem join_0_1 : (twinPrimeSegment 307298349 307363885).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 307298349 ≤ 307331117)
    (by decide : 307331117 ≤ 307363885) block2 block3

theorem join_1_0 : (twinPrimeSegment 307232813 307363885).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 307232813 ≤ 307298349)
    (by decide : 307298349 ≤ 307363885) join_0_0 join_0_1

theorem total : (twinPrimeSegment 307232813 307363885).card = 449 := join_1_0

end S146C08
end Sude.GeneratedTwinScan
