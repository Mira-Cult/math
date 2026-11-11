import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S193C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20148)) 405930029 405962797 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 405930029 405962797).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20148 405930029 405962797
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20149)) 405962797 405995565 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 405962797 405995565).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20149 405962797 405995565
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20150)) 405995565 406028333 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 405995565 406028333).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20150 405995565 406028333
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20150)) 406028333 406061101 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 406028333 406061101).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20150 406028333 406061101
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 405930029 405995565).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 405930029 ≤ 405962797)
    (by decide : 405962797 ≤ 405995565) block0 block1

theorem join_0_1 : (twinPrimeSegment 405995565 406061101).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 405995565 ≤ 406028333)
    (by decide : 406028333 ≤ 406061101) block2 block3

theorem join_1_0 : (twinPrimeSegment 405930029 406061101).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 405930029 ≤ 405995565)
    (by decide : 405995565 ≤ 406061101) join_0_0 join_0_1

theorem total : (twinPrimeSegment 405930029 406061101).card = 457 := join_1_0

end S193C09
end Sude.GeneratedTwinScan
