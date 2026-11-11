import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S210C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20995)) 440795181 440827949 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 440795181 440827949).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20995 440795181 440827949
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20996)) 440827949 440860717 = 92 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 440827949 440860717).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20996 440827949 440860717
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20997)) 440860717 440893485 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 440860717 440893485).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20997 440860717 440893485
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20998)) 440893485 440926253 = 93 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 440893485 440926253).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20998 440893485 440926253
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 440795181 440860717).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 440795181 ≤ 440827949)
    (by decide : 440827949 ≤ 440860717) block0 block1

theorem join_0_1 : (twinPrimeSegment 440860717 440926253).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 440860717 ≤ 440893485)
    (by decide : 440893485 ≤ 440926253) block2 block3

theorem join_1_0 : (twinPrimeSegment 440795181 440926253).card = 413 := by
  simpa using combineTwinPrimeSegments (by decide : 440795181 ≤ 440860717)
    (by decide : 440860717 ≤ 440926253) join_0_0 join_0_1

theorem total : (twinPrimeSegment 440795181 440926253).card = 413 := join_1_0

end S210C03
end Sude.GeneratedTwinScan
