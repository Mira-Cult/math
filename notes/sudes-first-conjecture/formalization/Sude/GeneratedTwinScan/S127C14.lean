import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S127C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16376)) 268173357 268206125 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 268173357 268206125).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16376 268173357 268206125
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16378)) 268206125 268238893 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 268206125 268238893).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16378 268206125 268238893
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16379)) 268238893 268271661 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 268238893 268271661).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16379 268238893 268271661
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16380)) 268271661 268304429 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 268271661 268304429).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16380 268271661 268304429
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 268173357 268238893).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 268173357 ≤ 268206125)
    (by decide : 268206125 ≤ 268238893) block0 block1

theorem join_0_1 : (twinPrimeSegment 268238893 268304429).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 268238893 ≤ 268271661)
    (by decide : 268271661 ≤ 268304429) block2 block3

theorem join_1_0 : (twinPrimeSegment 268173357 268304429).card = 452 := by
  simpa using combineTwinPrimeSegments (by decide : 268173357 ≤ 268238893)
    (by decide : 268238893 ≤ 268304429) join_0_0 join_0_1

theorem total : (twinPrimeSegment 268173357 268304429).card = 452 := join_1_0

end S127C14
end Sude.GeneratedTwinScan
