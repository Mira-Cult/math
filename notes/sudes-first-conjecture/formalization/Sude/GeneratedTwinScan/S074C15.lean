import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S074C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12537)) 157155373 157188141 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 157155373 157188141).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12537 157155373 157188141
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12538)) 157188141 157220909 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 157188141 157220909).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12538 157188141 157220909
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12540)) 157220909 157253677 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 157220909 157253677).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12540 157220909 157253677
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12541)) 157253677 157286445 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 157253677 157286445).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12541 157253677 157286445
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 157155373 157220909).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 157155373 ≤ 157188141)
    (by decide : 157188141 ≤ 157220909) block0 block1

theorem join_0_1 : (twinPrimeSegment 157220909 157286445).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 157220909 ≤ 157253677)
    (by decide : 157253677 ≤ 157286445) block2 block3

theorem join_1_0 : (twinPrimeSegment 157155373 157286445).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 157155373 ≤ 157220909)
    (by decide : 157220909 ≤ 157286445) join_0_0 join_0_1

theorem total : (twinPrimeSegment 157155373 157286445).card = 482 := join_1_0

end S074C15
end Sude.GeneratedTwinScan
