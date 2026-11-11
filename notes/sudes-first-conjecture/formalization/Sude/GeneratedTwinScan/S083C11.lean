import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S083C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13249)) 175505453 175538221 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 175505453 175538221).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13249 175505453 175538221
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13250)) 175538221 175570989 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 175538221 175570989).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13250 175538221 175570989
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13251)) 175570989 175603757 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 175570989 175603757).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13251 175570989 175603757
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13252)) 175603757 175636525 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 175603757 175636525).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13252 175603757 175636525
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 175505453 175570989).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 175505453 ≤ 175538221)
    (by decide : 175538221 ≤ 175570989) block0 block1

theorem join_0_1 : (twinPrimeSegment 175570989 175636525).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 175570989 ≤ 175603757)
    (by decide : 175603757 ≤ 175636525) block2 block3

theorem join_1_0 : (twinPrimeSegment 175505453 175636525).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 175505453 ≤ 175570989)
    (by decide : 175570989 ≤ 175636525) join_0_0 join_0_1

theorem total : (twinPrimeSegment 175505453 175636525).card = 461 := join_1_0

end S083C11
end Sude.GeneratedTwinScan
