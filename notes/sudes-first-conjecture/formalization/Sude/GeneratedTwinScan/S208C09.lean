import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S208C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20914)) 437387309 437420077 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 437387309 437420077).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20914 437387309 437420077
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20915)) 437420077 437452845 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 437420077 437452845).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20915 437420077 437452845
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20916)) 437452845 437485613 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 437452845 437485613).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20916 437452845 437485613
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20916)) 437485613 437518381 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 437485613 437518381).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20916 437485613 437518381
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 437387309 437452845).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 437387309 ≤ 437420077)
    (by decide : 437420077 ≤ 437452845) block0 block1

theorem join_0_1 : (twinPrimeSegment 437452845 437518381).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 437452845 ≤ 437485613)
    (by decide : 437485613 ≤ 437518381) block2 block3

theorem join_1_0 : (twinPrimeSegment 437387309 437518381).card = 410 := by
  simpa using combineTwinPrimeSegments (by decide : 437387309 ≤ 437452845)
    (by decide : 437452845 ≤ 437518381) join_0_0 join_0_1

theorem total : (twinPrimeSegment 437387309 437518381).card = 410 := join_1_0

end S208C09
end Sude.GeneratedTwinScan
