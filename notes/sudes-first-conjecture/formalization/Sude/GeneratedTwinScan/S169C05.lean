import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S169C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18844)) 355074093 355106861 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 355074093 355106861).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18844 355074093 355106861
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18845)) 355106861 355139629 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 355106861 355139629).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18845 355106861 355139629
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18846)) 355139629 355172397 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 355139629 355172397).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18846 355139629 355172397
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18846)) 355172397 355205165 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 355172397 355205165).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18846 355172397 355205165
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 355074093 355139629).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 355074093 ≤ 355106861)
    (by decide : 355106861 ≤ 355139629) block0 block1

theorem join_0_1 : (twinPrimeSegment 355139629 355205165).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 355139629 ≤ 355172397)
    (by decide : 355172397 ≤ 355205165) block2 block3

theorem join_1_0 : (twinPrimeSegment 355074093 355205165).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 355074093 ≤ 355139629)
    (by decide : 355139629 ≤ 355205165) join_0_0 join_0_1

theorem total : (twinPrimeSegment 355074093 355205165).card = 450 := join_1_0

end S169C05
end Sude.GeneratedTwinScan
