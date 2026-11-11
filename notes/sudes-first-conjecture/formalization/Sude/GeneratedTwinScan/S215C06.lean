import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S215C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21253)) 451674157 451706925 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 451674157 451706925).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21253 451674157 451706925
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21254)) 451706925 451739693 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 451706925 451739693).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21254 451706925 451739693
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21254)) 451739693 451772461 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 451739693 451772461).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21254 451739693 451772461
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21255)) 451772461 451805229 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 451772461 451805229).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21255 451772461 451805229
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 451674157 451739693).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 451674157 ≤ 451706925)
    (by decide : 451706925 ≤ 451739693) block0 block1

theorem join_0_1 : (twinPrimeSegment 451739693 451805229).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 451739693 ≤ 451772461)
    (by decide : 451772461 ≤ 451805229) block2 block3

theorem join_1_0 : (twinPrimeSegment 451674157 451805229).card = 424 := by
  simpa using combineTwinPrimeSegments (by decide : 451674157 ≤ 451739693)
    (by decide : 451739693 ≤ 451805229) join_0_0 join_0_1

theorem total : (twinPrimeSegment 451674157 451805229).card = 424 := join_1_0

end S215C06
end Sude.GeneratedTwinScan
