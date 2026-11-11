import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S093C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13990)) 195690541 195723309 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 195690541 195723309).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13990 195690541 195723309
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13991)) 195723309 195756077 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 195723309 195756077).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13991 195723309 195756077
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13992)) 195756077 195788845 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 195756077 195788845).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13992 195756077 195788845
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13993)) 195788845 195821613 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 195788845 195821613).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13993 195788845 195821613
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 195690541 195756077).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 195690541 ≤ 195723309)
    (by decide : 195723309 ≤ 195756077) block0 block1

theorem join_0_1 : (twinPrimeSegment 195756077 195821613).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 195756077 ≤ 195788845)
    (by decide : 195788845 ≤ 195821613) block2 block3

theorem join_1_0 : (twinPrimeSegment 195690541 195821613).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 195690541 ≤ 195756077)
    (by decide : 195756077 ≤ 195821613) join_0_0 join_0_1

theorem total : (twinPrimeSegment 195690541 195821613).card = 449 := join_1_0

end S093C05
end Sude.GeneratedTwinScan
