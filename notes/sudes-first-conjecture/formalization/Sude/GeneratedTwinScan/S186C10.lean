import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S186C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19784)) 391381037 391413805 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 391381037 391413805).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19784 391381037 391413805
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19785)) 391413805 391446573 = 96 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 391413805 391446573).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19785 391413805 391446573
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19785)) 391446573 391479341 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 391446573 391479341).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19785 391446573 391479341
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19786)) 391479341 391512109 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 391479341 391512109).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19786 391479341 391512109
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 391381037 391446573).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 391381037 ≤ 391413805)
    (by decide : 391413805 ≤ 391446573) block0 block1

theorem join_0_1 : (twinPrimeSegment 391446573 391512109).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 391446573 ≤ 391479341)
    (by decide : 391479341 ≤ 391512109) block2 block3

theorem join_1_0 : (twinPrimeSegment 391381037 391512109).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 391381037 ≤ 391446573)
    (by decide : 391446573 ≤ 391512109) join_0_0 join_0_1

theorem total : (twinPrimeSegment 391381037 391512109).card = 443 := join_1_0

end S186C10
end Sude.GeneratedTwinScan
