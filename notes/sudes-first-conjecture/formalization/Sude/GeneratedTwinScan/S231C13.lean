import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S231C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22049)) 486146093 486178861 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 486146093 486178861).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22049 486146093 486178861
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22050)) 486178861 486211629 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 486178861 486211629).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22050 486178861 486211629
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22050)) 486211629 486244397 = 89 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 486211629 486244397).card = 89 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22050 486211629 486244397
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22051)) 486244397 486277165 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 486244397 486277165).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22051 486244397 486277165
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 486146093 486211629).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 486146093 ≤ 486178861)
    (by decide : 486178861 ≤ 486211629) block0 block1

theorem join_0_1 : (twinPrimeSegment 486211629 486277165).card = 199 := by
  simpa using combineTwinPrimeSegments (by decide : 486211629 ≤ 486244397)
    (by decide : 486244397 ≤ 486277165) block2 block3

theorem join_1_0 : (twinPrimeSegment 486146093 486277165).card = 424 := by
  simpa using combineTwinPrimeSegments (by decide : 486146093 ≤ 486211629)
    (by decide : 486211629 ≤ 486277165) join_0_0 join_0_1

theorem total : (twinPrimeSegment 486146093 486277165).card = 424 := join_1_0

end S231C13
end Sude.GeneratedTwinScan
