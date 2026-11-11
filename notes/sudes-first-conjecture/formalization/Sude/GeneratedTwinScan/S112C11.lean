import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S112C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15373)) 236322861 236355629 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 236322861 236355629).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15373 236322861 236355629
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15374)) 236355629 236388397 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 236355629 236388397).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15374 236355629 236388397
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15375)) 236388397 236421165 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 236388397 236421165).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15375 236388397 236421165
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15377)) 236421165 236453933 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 236421165 236453933).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15377 236421165 236453933
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 236322861 236388397).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 236322861 ≤ 236355629)
    (by decide : 236355629 ≤ 236388397) block0 block1

theorem join_0_1 : (twinPrimeSegment 236388397 236453933).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 236388397 ≤ 236421165)
    (by decide : 236421165 ≤ 236453933) block2 block3

theorem join_1_0 : (twinPrimeSegment 236322861 236453933).card = 486 := by
  simpa using combineTwinPrimeSegments (by decide : 236322861 ≤ 236388397)
    (by decide : 236388397 ≤ 236453933) join_0_0 join_0_1

theorem total : (twinPrimeSegment 236322861 236453933).card = 486 := join_1_0

end S112C11
end Sude.GeneratedTwinScan
