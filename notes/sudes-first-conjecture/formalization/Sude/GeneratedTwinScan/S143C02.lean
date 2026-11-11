import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S143C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17325)) 300154925 300187693 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 300154925 300187693).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17325 300154925 300187693
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17326)) 300187693 300220461 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 300187693 300220461).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17326 300187693 300220461
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17327)) 300220461 300253229 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 300220461 300253229).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17327 300220461 300253229
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17328)) 300253229 300285997 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 300253229 300285997).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17328 300253229 300285997
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 300154925 300220461).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 300154925 ≤ 300187693)
    (by decide : 300187693 ≤ 300220461) block0 block1

theorem join_0_1 : (twinPrimeSegment 300220461 300285997).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 300220461 ≤ 300253229)
    (by decide : 300253229 ≤ 300285997) block2 block3

theorem join_1_0 : (twinPrimeSegment 300154925 300285997).card = 474 := by
  simpa using combineTwinPrimeSegments (by decide : 300154925 ≤ 300220461)
    (by decide : 300220461 ≤ 300285997) join_0_0 join_0_1

theorem total : (twinPrimeSegment 300154925 300285997).card = 474 := join_1_0

end S143C02
end Sude.GeneratedTwinScan
