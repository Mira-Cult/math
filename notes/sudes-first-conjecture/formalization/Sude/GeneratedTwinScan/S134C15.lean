import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S134C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16823)) 282984493 283017261 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 282984493 283017261).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16823 282984493 283017261
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16824)) 283017261 283050029 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 283017261 283050029).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16824 283017261 283050029
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16825)) 283050029 283082797 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 283050029 283082797).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16825 283050029 283082797
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16826)) 283082797 283115565 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 283082797 283115565).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16826 283082797 283115565
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 282984493 283050029).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 282984493 ≤ 283017261)
    (by decide : 283017261 ≤ 283050029) block0 block1

theorem join_0_1 : (twinPrimeSegment 283050029 283115565).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 283050029 ≤ 283082797)
    (by decide : 283082797 ≤ 283115565) block2 block3

theorem join_1_0 : (twinPrimeSegment 282984493 283115565).card = 459 := by
  simpa using combineTwinPrimeSegments (by decide : 282984493 ≤ 283050029)
    (by decide : 283050029 ≤ 283115565) join_0_0 join_0_1

theorem total : (twinPrimeSegment 282984493 283115565).card = 459 := join_1_0

end S134C15
end Sude.GeneratedTwinScan
