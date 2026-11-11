import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S078C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12847)) 165019693 165052461 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 165019693 165052461).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12847 165019693 165052461
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12848)) 165052461 165085229 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 165052461 165085229).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12848 165052461 165085229
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12849)) 165085229 165117997 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 165085229 165117997).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12849 165085229 165117997
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12851)) 165117997 165150765 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 165117997 165150765).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12851 165117997 165150765
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 165019693 165085229).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 165019693 ≤ 165052461)
    (by decide : 165052461 ≤ 165085229) block0 block1

theorem join_0_1 : (twinPrimeSegment 165085229 165150765).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 165085229 ≤ 165117997)
    (by decide : 165117997 ≤ 165150765) block2 block3

theorem join_1_0 : (twinPrimeSegment 165019693 165150765).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 165019693 ≤ 165085229)
    (by decide : 165085229 ≤ 165150765) join_0_0 join_0_1

theorem total : (twinPrimeSegment 165019693 165150765).card = 465 := join_1_0

end S078C11
end Sude.GeneratedTwinScan
