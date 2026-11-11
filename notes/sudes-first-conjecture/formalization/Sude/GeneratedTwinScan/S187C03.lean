import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S187C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19813)) 392560685 392593453 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 392560685 392593453).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19813 392560685 392593453
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19814)) 392593453 392626221 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 392593453 392626221).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19814 392593453 392626221
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19815)) 392626221 392658989 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 392626221 392658989).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19815 392626221 392658989
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19816)) 392658989 392691757 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 392658989 392691757).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19816 392658989 392691757
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 392560685 392626221).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 392560685 ≤ 392593453)
    (by decide : 392593453 ≤ 392626221) block0 block1

theorem join_0_1 : (twinPrimeSegment 392626221 392691757).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 392626221 ≤ 392658989)
    (by decide : 392658989 ≤ 392691757) block2 block3

theorem join_1_0 : (twinPrimeSegment 392560685 392691757).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 392560685 ≤ 392626221)
    (by decide : 392626221 ≤ 392691757) join_0_0 join_0_1

theorem total : (twinPrimeSegment 392560685 392691757).card = 454 := join_1_0

end S187C03
end Sude.GeneratedTwinScan
