import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S151C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17825)) 317718573 317751341 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 317718573 317751341).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17825 317718573 317751341
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17826)) 317751341 317784109 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 317751341 317784109).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17826 317751341 317784109
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17827)) 317784109 317816877 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 317784109 317816877).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17827 317784109 317816877
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17828)) 317816877 317849645 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 317816877 317849645).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17828 317816877 317849645
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 317718573 317784109).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 317718573 ≤ 317751341)
    (by decide : 317751341 ≤ 317784109) block0 block1

theorem join_0_1 : (twinPrimeSegment 317784109 317849645).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 317784109 ≤ 317816877)
    (by decide : 317816877 ≤ 317849645) block2 block3

theorem join_1_0 : (twinPrimeSegment 317718573 317849645).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 317718573 ≤ 317784109)
    (by decide : 317784109 ≤ 317849645) join_0_0 join_0_1

theorem total : (twinPrimeSegment 317718573 317849645).card = 426 := join_1_0

end S151C08
end Sude.GeneratedTwinScan
