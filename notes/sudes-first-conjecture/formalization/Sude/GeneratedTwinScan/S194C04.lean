import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S194C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20184)) 407371821 407404589 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 407371821 407404589).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20184 407371821 407404589
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20185)) 407404589 407437357 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 407404589 407437357).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20185 407404589 407437357
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20185)) 407437357 407470125 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 407437357 407470125).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20185 407437357 407470125
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20186)) 407470125 407502893 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 407470125 407502893).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20186 407470125 407502893
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 407371821 407437357).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 407371821 ≤ 407404589)
    (by decide : 407404589 ≤ 407437357) block0 block1

theorem join_0_1 : (twinPrimeSegment 407437357 407502893).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 407437357 ≤ 407470125)
    (by decide : 407470125 ≤ 407502893) block2 block3

theorem join_1_0 : (twinPrimeSegment 407371821 407502893).card = 423 := by
  simpa using combineTwinPrimeSegments (by decide : 407371821 ≤ 407437357)
    (by decide : 407437357 ≤ 407502893) join_0_0 join_0_1

theorem total : (twinPrimeSegment 407371821 407502893).card = 423 := join_1_0

end S194C04
end Sude.GeneratedTwinScan
