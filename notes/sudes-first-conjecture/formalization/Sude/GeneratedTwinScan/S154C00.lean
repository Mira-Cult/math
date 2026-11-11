import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S154C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17972)) 322961453 322994221 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 322961453 322994221).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17972 322961453 322994221
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17972)) 322994221 323026989 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 322994221 323026989).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17972 322994221 323026989
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17973)) 323026989 323059757 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 323026989 323059757).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17973 323026989 323059757
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17974)) 323059757 323092525 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 323059757 323092525).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17974 323059757 323092525
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 322961453 323026989).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 322961453 ≤ 322994221)
    (by decide : 322994221 ≤ 323026989) block0 block1

theorem join_0_1 : (twinPrimeSegment 323026989 323092525).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 323026989 ≤ 323059757)
    (by decide : 323059757 ≤ 323092525) block2 block3

theorem join_1_0 : (twinPrimeSegment 322961453 323092525).card = 498 := by
  simpa using combineTwinPrimeSegments (by decide : 322961453 ≤ 323026989)
    (by decide : 323026989 ≤ 323092525) join_0_0 join_0_1

theorem total : (twinPrimeSegment 322961453 323092525).card = 498 := join_1_0

end S154C00
end Sude.GeneratedTwinScan
