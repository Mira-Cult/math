import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S199C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20467)) 418906157 418938925 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 418906157 418938925).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20467 418906157 418938925
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20468)) 418938925 418971693 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 418938925 418971693).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20468 418938925 418971693
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20469)) 418971693 419004461 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 418971693 419004461).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20469 418971693 419004461
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20470)) 419004461 419037229 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 419004461 419037229).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20470 419004461 419037229
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 418906157 418971693).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 418906157 ≤ 418938925)
    (by decide : 418938925 ≤ 418971693) block0 block1

theorem join_0_1 : (twinPrimeSegment 418971693 419037229).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 418971693 ≤ 419004461)
    (by decide : 419004461 ≤ 419037229) block2 block3

theorem join_1_0 : (twinPrimeSegment 418906157 419037229).card = 427 := by
  simpa using combineTwinPrimeSegments (by decide : 418906157 ≤ 418971693)
    (by decide : 418971693 ≤ 419037229) join_0_0 join_0_1

theorem total : (twinPrimeSegment 418906157 419037229).card = 427 := join_1_0

end S199C12
end Sude.GeneratedTwinScan
