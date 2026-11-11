import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S227C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21855)) 477626413 477659181 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 477626413 477659181).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21855 477626413 477659181
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21856)) 477659181 477691949 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 477659181 477691949).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21856 477659181 477691949
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21856)) 477691949 477724717 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 477691949 477724717).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21856 477691949 477724717
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21857)) 477724717 477757485 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 477724717 477757485).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21857 477724717 477757485
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 477626413 477691949).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 477626413 ≤ 477659181)
    (by decide : 477659181 ≤ 477691949) block0 block1

theorem join_0_1 : (twinPrimeSegment 477691949 477757485).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 477691949 ≤ 477724717)
    (by decide : 477724717 ≤ 477757485) block2 block3

theorem join_1_0 : (twinPrimeSegment 477626413 477757485).card = 433 := by
  simpa using combineTwinPrimeSegments (by decide : 477626413 ≤ 477691949)
    (by decide : 477691949 ≤ 477757485) join_0_0 join_0_1

theorem total : (twinPrimeSegment 477626413 477757485).card = 433 := join_1_0

end S227C12
end Sude.GeneratedTwinScan
