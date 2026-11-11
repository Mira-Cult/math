import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S100C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14505)) 210370605 210403373 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 210370605 210403373).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14505 210370605 210403373
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14506)) 210403373 210436141 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 210403373 210436141).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14506 210403373 210436141
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14507)) 210436141 210468909 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 210436141 210468909).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14507 210436141 210468909
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14508)) 210468909 210501677 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 210468909 210501677).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14508 210468909 210501677
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 210370605 210436141).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 210370605 ≤ 210403373)
    (by decide : 210403373 ≤ 210436141) block0 block1

theorem join_0_1 : (twinPrimeSegment 210436141 210501677).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 210436141 ≤ 210468909)
    (by decide : 210468909 ≤ 210501677) block2 block3

theorem join_1_0 : (twinPrimeSegment 210370605 210501677).card = 470 := by
  simpa using combineTwinPrimeSegments (by decide : 210370605 ≤ 210436141)
    (by decide : 210436141 ≤ 210501677) join_0_0 join_0_1

theorem total : (twinPrimeSegment 210370605 210501677).card = 470 := join_1_0

end S100C05
end Sude.GeneratedTwinScan
