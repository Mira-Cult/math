import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S111C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15292)) 233832493 233865261 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 233832493 233865261).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15292 233832493 233865261
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15293)) 233865261 233898029 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 233865261 233898029).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15293 233865261 233898029
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15294)) 233898029 233930797 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 233898029 233930797).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15294 233898029 233930797
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15295)) 233930797 233963565 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 233930797 233963565).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15295 233930797 233963565
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 233832493 233898029).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 233832493 ≤ 233865261)
    (by decide : 233865261 ≤ 233898029) block0 block1

theorem join_0_1 : (twinPrimeSegment 233898029 233963565).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 233898029 ≤ 233930797)
    (by decide : 233930797 ≤ 233963565) block2 block3

theorem join_1_0 : (twinPrimeSegment 233832493 233963565).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 233832493 ≤ 233898029)
    (by decide : 233898029 ≤ 233963565) join_0_0 join_0_1

theorem total : (twinPrimeSegment 233832493 233963565).card = 464 := join_1_0

end S111C08
end Sude.GeneratedTwinScan
