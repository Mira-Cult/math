import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S099C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14469)) 209322029 209354797 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 209322029 209354797).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14469 209322029 209354797
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14470)) 209354797 209387565 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 209354797 209387565).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14470 209354797 209387565
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14471)) 209387565 209420333 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 209387565 209420333).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14471 209387565 209420333
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14472)) 209420333 209453101 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 209420333 209453101).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14472 209420333 209453101
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 209322029 209387565).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 209322029 ≤ 209354797)
    (by decide : 209354797 ≤ 209387565) block0 block1

theorem join_0_1 : (twinPrimeSegment 209387565 209453101).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 209387565 ≤ 209420333)
    (by decide : 209420333 ≤ 209453101) block2 block3

theorem join_1_0 : (twinPrimeSegment 209322029 209453101).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 209322029 ≤ 209387565)
    (by decide : 209387565 ≤ 209453101) join_0_0 join_0_1

theorem total : (twinPrimeSegment 209322029 209453101).card = 468 := join_1_0

end S099C13
end Sude.GeneratedTwinScan
