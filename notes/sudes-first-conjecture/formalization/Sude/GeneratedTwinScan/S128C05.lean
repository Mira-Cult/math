import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S128C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16404)) 269090861 269123629 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 269090861 269123629).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16404 269090861 269123629
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16405)) 269123629 269156397 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 269123629 269156397).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16405 269123629 269156397
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16406)) 269156397 269189165 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 269156397 269189165).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16406 269156397 269189165
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16407)) 269189165 269221933 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 269189165 269221933).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16407 269189165 269221933
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 269090861 269156397).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 269090861 ≤ 269123629)
    (by decide : 269123629 ≤ 269156397) block0 block1

theorem join_0_1 : (twinPrimeSegment 269156397 269221933).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 269156397 ≤ 269189165)
    (by decide : 269189165 ≤ 269221933) block2 block3

theorem join_1_0 : (twinPrimeSegment 269090861 269221933).card = 493 := by
  simpa using combineTwinPrimeSegments (by decide : 269090861 ≤ 269156397)
    (by decide : 269156397 ≤ 269221933) join_0_0 join_0_1

theorem total : (twinPrimeSegment 269090861 269221933).card = 493 := join_1_0

end S128C05
end Sude.GeneratedTwinScan
