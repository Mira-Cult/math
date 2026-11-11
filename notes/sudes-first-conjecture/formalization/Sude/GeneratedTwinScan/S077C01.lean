import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S077C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12713)) 161611821 161644589 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 161611821 161644589).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12713 161611821 161644589
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12715)) 161644589 161677357 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 161644589 161677357).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12715 161644589 161677357
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12716)) 161677357 161710125 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 161677357 161710125).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12716 161677357 161710125
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12717)) 161710125 161742893 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 161710125 161742893).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12717 161710125 161742893
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 161611821 161677357).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 161611821 ≤ 161644589)
    (by decide : 161644589 ≤ 161677357) block0 block1

theorem join_0_1 : (twinPrimeSegment 161677357 161742893).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 161677357 ≤ 161710125)
    (by decide : 161710125 ≤ 161742893) block2 block3

theorem join_1_0 : (twinPrimeSegment 161611821 161742893).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 161611821 ≤ 161677357)
    (by decide : 161677357 ≤ 161742893) join_0_0 join_0_1

theorem total : (twinPrimeSegment 161611821 161742893).card = 463 := join_1_0

end S077C01
end Sude.GeneratedTwinScan
