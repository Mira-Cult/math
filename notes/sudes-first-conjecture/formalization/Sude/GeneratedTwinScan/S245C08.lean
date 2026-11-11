import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S245C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22691)) 514850861 514883629 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 514850861 514883629).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22691 514850861 514883629
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22691)) 514883629 514916397 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 514883629 514916397).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22691 514883629 514916397
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22692)) 514916397 514949165 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 514916397 514949165).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22692 514916397 514949165
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22693)) 514949165 514981933 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 514949165 514981933).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22693 514949165 514981933
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 514850861 514916397).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 514850861 ≤ 514883629)
    (by decide : 514883629 ≤ 514916397) block0 block1

theorem join_0_1 : (twinPrimeSegment 514916397 514981933).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 514916397 ≤ 514949165)
    (by decide : 514949165 ≤ 514981933) block2 block3

theorem join_1_0 : (twinPrimeSegment 514850861 514981933).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 514850861 ≤ 514916397)
    (by decide : 514916397 ≤ 514981933) join_0_0 join_0_1

theorem total : (twinPrimeSegment 514850861 514981933).card = 442 := join_1_0

end S245C08
end Sude.GeneratedTwinScan
