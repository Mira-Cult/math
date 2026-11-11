import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S116C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15610)) 243662893 243695661 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 243662893 243695661).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15610 243662893 243695661
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15611)) 243695661 243728429 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 243695661 243728429).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15611 243695661 243728429
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15612)) 243728429 243761197 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 243728429 243761197).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15612 243728429 243761197
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15613)) 243761197 243793965 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 243761197 243793965).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15613 243761197 243793965
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 243662893 243728429).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 243662893 ≤ 243695661)
    (by decide : 243695661 ≤ 243728429) block0 block1

theorem join_0_1 : (twinPrimeSegment 243728429 243793965).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 243728429 ≤ 243761197)
    (by decide : 243761197 ≤ 243793965) block2 block3

theorem join_1_0 : (twinPrimeSegment 243662893 243793965).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 243662893 ≤ 243728429)
    (by decide : 243728429 ≤ 243793965) join_0_0 join_0_1

theorem total : (twinPrimeSegment 243662893 243793965).card = 439 := join_1_0

end S116C03
end Sude.GeneratedTwinScan
