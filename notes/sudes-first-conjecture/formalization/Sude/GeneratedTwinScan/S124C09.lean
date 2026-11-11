import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S124C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16163)) 261226541 261259309 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 261226541 261259309).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16163 261226541 261259309
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16164)) 261259309 261292077 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 261259309 261292077).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16164 261259309 261292077
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16165)) 261292077 261324845 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 261292077 261324845).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16165 261292077 261324845
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16166)) 261324845 261357613 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 261324845 261357613).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16166 261324845 261357613
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 261226541 261292077).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 261226541 ≤ 261259309)
    (by decide : 261259309 ≤ 261292077) block0 block1

theorem join_0_1 : (twinPrimeSegment 261292077 261357613).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 261292077 ≤ 261324845)
    (by decide : 261324845 ≤ 261357613) block2 block3

theorem join_1_0 : (twinPrimeSegment 261226541 261357613).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 261226541 ≤ 261292077)
    (by decide : 261292077 ≤ 261357613) join_0_0 join_0_1

theorem total : (twinPrimeSegment 261226541 261357613).card = 447 := join_1_0

end S124C09
end Sude.GeneratedTwinScan
