import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S118C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15790)) 249298989 249331757 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 249298989 249331757).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15790 249298989 249331757
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15791)) 249331757 249364525 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 249331757 249364525).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15791 249331757 249364525
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15792)) 249364525 249397293 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 249364525 249397293).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15792 249364525 249397293
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15793)) 249397293 249430061 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 249397293 249430061).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15793 249397293 249430061
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 249298989 249364525).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 249298989 ≤ 249331757)
    (by decide : 249331757 ≤ 249364525) block0 block1

theorem join_0_1 : (twinPrimeSegment 249364525 249430061).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 249364525 ≤ 249397293)
    (by decide : 249397293 ≤ 249430061) block2 block3

theorem join_1_0 : (twinPrimeSegment 249298989 249430061).card = 472 := by
  simpa using combineTwinPrimeSegments (by decide : 249298989 ≤ 249364525)
    (by decide : 249364525 ≤ 249430061) join_0_0 join_0_1

theorem total : (twinPrimeSegment 249298989 249430061).card = 472 := join_1_0

end S118C14
end Sude.GeneratedTwinScan
