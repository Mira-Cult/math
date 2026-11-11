import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S076C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12698)) 161218605 161251373 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 161218605 161251373).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12698 161218605 161251373
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12699)) 161251373 161284141 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 161251373 161284141).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12699 161251373 161284141
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12701)) 161284141 161316909 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 161284141 161316909).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12701 161284141 161316909
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12702)) 161316909 161349677 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 161316909 161349677).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12702 161316909 161349677
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 161218605 161284141).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 161218605 ≤ 161251373)
    (by decide : 161251373 ≤ 161284141) block0 block1

theorem join_0_1 : (twinPrimeSegment 161284141 161349677).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 161284141 ≤ 161316909)
    (by decide : 161316909 ≤ 161349677) block2 block3

theorem join_1_0 : (twinPrimeSegment 161218605 161349677).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 161218605 ≤ 161284141)
    (by decide : 161284141 ≤ 161349677) join_0_0 join_0_1

theorem total : (twinPrimeSegment 161218605 161349677).card = 464 := join_1_0

end S076C14
end Sude.GeneratedTwinScan
