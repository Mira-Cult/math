import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S208C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20905)) 436994093 437026861 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 436994093 437026861).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20905 436994093 437026861
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20905)) 437026861 437059629 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 437026861 437059629).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20905 437026861 437059629
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20906)) 437059629 437092397 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 437059629 437092397).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20906 437059629 437092397
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20907)) 437092397 437125165 = 94 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 437092397 437125165).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20907 437092397 437125165
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 436994093 437059629).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 436994093 ≤ 437026861)
    (by decide : 437026861 ≤ 437059629) block0 block1

theorem join_0_1 : (twinPrimeSegment 437059629 437125165).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 437059629 ≤ 437092397)
    (by decide : 437092397 ≤ 437125165) block2 block3

theorem join_1_0 : (twinPrimeSegment 436994093 437125165).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 436994093 ≤ 437059629)
    (by decide : 437059629 ≤ 437125165) join_0_0 join_0_1

theorem total : (twinPrimeSegment 436994093 437125165).card = 438 := join_1_0

end S208C06
end Sude.GeneratedTwinScan
