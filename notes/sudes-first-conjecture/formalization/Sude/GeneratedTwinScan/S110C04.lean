import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S110C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15206)) 231211053 231243821 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 231211053 231243821).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15206 231211053 231243821
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15207)) 231243821 231276589 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 231243821 231276589).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15207 231243821 231276589
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15208)) 231276589 231309357 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 231276589 231309357).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15208 231276589 231309357
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15209)) 231309357 231342125 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 231309357 231342125).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15209 231309357 231342125
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 231211053 231276589).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 231211053 ≤ 231243821)
    (by decide : 231243821 ≤ 231276589) block0 block1

theorem join_0_1 : (twinPrimeSegment 231276589 231342125).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 231276589 ≤ 231309357)
    (by decide : 231309357 ≤ 231342125) block2 block3

theorem join_1_0 : (twinPrimeSegment 231211053 231342125).card = 475 := by
  simpa using combineTwinPrimeSegments (by decide : 231211053 ≤ 231276589)
    (by decide : 231276589 ≤ 231342125) join_0_0 join_0_1

theorem total : (twinPrimeSegment 231211053 231342125).card = 475 := join_1_0

end S110C04
end Sude.GeneratedTwinScan
