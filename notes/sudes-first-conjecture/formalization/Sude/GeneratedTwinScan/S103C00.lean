import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S103C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14698)) 216006701 216039469 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 216006701 216039469).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14698 216006701 216039469
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14699)) 216039469 216072237 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 216039469 216072237).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14699 216039469 216072237
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14700)) 216072237 216105005 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 216072237 216105005).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14700 216072237 216105005
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14701)) 216105005 216137773 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 216105005 216137773).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14701 216105005 216137773
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 216006701 216072237).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 216006701 ≤ 216039469)
    (by decide : 216039469 ≤ 216072237) block0 block1

theorem join_0_1 : (twinPrimeSegment 216072237 216137773).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 216072237 ≤ 216105005)
    (by decide : 216105005 ≤ 216137773) block2 block3

theorem join_1_0 : (twinPrimeSegment 216006701 216137773).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 216006701 ≤ 216072237)
    (by decide : 216072237 ≤ 216137773) join_0_0 join_0_1

theorem total : (twinPrimeSegment 216006701 216137773).card = 462 := join_1_0

end S103C00
end Sude.GeneratedTwinScan
