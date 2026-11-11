import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S225C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21747)) 472907821 472940589 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 472907821 472940589).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21747 472907821 472940589
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21747)) 472940589 472973357 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 472940589 472973357).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21747 472940589 472973357
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21748)) 472973357 473006125 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 472973357 473006125).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21748 472973357 473006125
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21749)) 473006125 473038893 = 91 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 473006125 473038893).card = 91 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21749 473006125 473038893
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 472907821 472973357).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 472907821 ≤ 472940589)
    (by decide : 472940589 ≤ 472973357) block0 block1

theorem join_0_1 : (twinPrimeSegment 472973357 473038893).card = 199 := by
  simpa using combineTwinPrimeSegments (by decide : 472973357 ≤ 473006125)
    (by decide : 473006125 ≤ 473038893) block2 block3

theorem join_1_0 : (twinPrimeSegment 472907821 473038893).card = 424 := by
  simpa using combineTwinPrimeSegments (by decide : 472907821 ≤ 472973357)
    (by decide : 472973357 ≤ 473038893) join_0_0 join_0_1

theorem total : (twinPrimeSegment 472907821 473038893).card = 424 := join_1_0

end S225C08
end Sude.GeneratedTwinScan
