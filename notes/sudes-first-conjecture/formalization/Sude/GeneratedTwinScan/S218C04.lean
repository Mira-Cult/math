import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S218C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21394)) 457703469 457736237 = 93 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 457703469 457736237).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21394 457703469 457736237
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21395)) 457736237 457769005 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 457736237 457769005).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21395 457736237 457769005
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21396)) 457769005 457801773 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 457769005 457801773).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21396 457769005 457801773
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21397)) 457801773 457834541 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 457801773 457834541).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21397 457801773 457834541
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 457703469 457769005).card = 198 := by
  simpa using combineTwinPrimeSegments (by decide : 457703469 ≤ 457736237)
    (by decide : 457736237 ≤ 457769005) block0 block1

theorem join_0_1 : (twinPrimeSegment 457769005 457834541).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 457769005 ≤ 457801773)
    (by decide : 457801773 ≤ 457834541) block2 block3

theorem join_1_0 : (twinPrimeSegment 457703469 457834541).card = 404 := by
  simpa using combineTwinPrimeSegments (by decide : 457703469 ≤ 457769005)
    (by decide : 457769005 ≤ 457834541) join_0_0 join_0_1

theorem total : (twinPrimeSegment 457703469 457834541).card = 404 := join_1_0

end S218C04
end Sude.GeneratedTwinScan
