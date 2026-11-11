import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S172C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19044)) 362676269 362709037 = 97 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 362676269 362709037).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19044 362676269 362709037
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19045)) 362709037 362741805 = 92 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 362709037 362741805).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19045 362709037 362741805
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19046)) 362741805 362774573 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 362741805 362774573).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19046 362741805 362774573
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19047)) 362774573 362807341 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 362774573 362807341).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19047 362774573 362807341
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 362676269 362741805).card = 189 := by
  simpa using combineTwinPrimeSegments (by decide : 362676269 ≤ 362709037)
    (by decide : 362709037 ≤ 362741805) block0 block1

theorem join_0_1 : (twinPrimeSegment 362741805 362807341).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 362741805 ≤ 362774573)
    (by decide : 362774573 ≤ 362807341) block2 block3

theorem join_1_0 : (twinPrimeSegment 362676269 362807341).card = 405 := by
  simpa using combineTwinPrimeSegments (by decide : 362676269 ≤ 362741805)
    (by decide : 362741805 ≤ 362807341) join_0_0 join_0_1

theorem total : (twinPrimeSegment 362676269 362807341).card = 405 := join_1_0

end S172C15
end Sude.GeneratedTwinScan
