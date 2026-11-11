import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S231C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22013)) 484573229 484605997 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 484573229 484605997).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22013 484573229 484605997
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22014)) 484605997 484638765 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 484605997 484638765).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22014 484605997 484638765
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22015)) 484638765 484671533 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 484638765 484671533).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22015 484638765 484671533
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22016)) 484671533 484704301 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 484671533 484704301).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22016 484671533 484704301
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 484573229 484638765).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 484573229 ≤ 484605997)
    (by decide : 484605997 ≤ 484638765) block0 block1

theorem join_0_1 : (twinPrimeSegment 484638765 484704301).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 484638765 ≤ 484671533)
    (by decide : 484671533 ≤ 484704301) block2 block3

theorem join_1_0 : (twinPrimeSegment 484573229 484704301).card = 413 := by
  simpa using combineTwinPrimeSegments (by decide : 484573229 ≤ 484638765)
    (by decide : 484638765 ≤ 484704301) join_0_0 join_0_1

theorem total : (twinPrimeSegment 484573229 484704301).card = 413 := join_1_0

end S231C01
end Sude.GeneratedTwinScan
