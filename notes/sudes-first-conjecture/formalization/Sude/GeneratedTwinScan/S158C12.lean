import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S158C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18247)) 332922925 332955693 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 332922925 332955693).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18247 332922925 332955693
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18247)) 332955693 332988461 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 332955693 332988461).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18247 332955693 332988461
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18248)) 332988461 333021229 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 332988461 333021229).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18248 332988461 333021229
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18249)) 333021229 333053997 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 333021229 333053997).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18249 333021229 333053997
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 332922925 332988461).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 332922925 ≤ 332955693)
    (by decide : 332955693 ≤ 332988461) block0 block1

theorem join_0_1 : (twinPrimeSegment 332988461 333053997).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 332988461 ≤ 333021229)
    (by decide : 333021229 ≤ 333053997) block2 block3

theorem join_1_0 : (twinPrimeSegment 332922925 333053997).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 332922925 ≤ 332988461)
    (by decide : 332988461 ≤ 333053997) join_0_0 join_0_1

theorem total : (twinPrimeSegment 332922925 333053997).card = 461 := join_1_0

end S158C12
end Sude.GeneratedTwinScan
