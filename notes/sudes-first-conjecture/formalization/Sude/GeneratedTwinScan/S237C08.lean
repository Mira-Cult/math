import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S237C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22318)) 498073645 498106413 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 498073645 498106413).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22318 498073645 498106413
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22319)) 498106413 498139181 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 498106413 498139181).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22319 498106413 498139181
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22319)) 498139181 498171949 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 498139181 498171949).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22319 498139181 498171949
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22320)) 498171949 498204717 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 498171949 498204717).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22320 498171949 498204717
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 498073645 498139181).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 498073645 ≤ 498106413)
    (by decide : 498106413 ≤ 498139181) block0 block1

theorem join_0_1 : (twinPrimeSegment 498139181 498204717).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 498139181 ≤ 498171949)
    (by decide : 498171949 ≤ 498204717) block2 block3

theorem join_1_0 : (twinPrimeSegment 498073645 498204717).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 498073645 ≤ 498139181)
    (by decide : 498139181 ≤ 498204717) join_0_0 join_0_1

theorem total : (twinPrimeSegment 498073645 498204717).card = 456 := join_1_0

end S237C08
end Sude.GeneratedTwinScan
