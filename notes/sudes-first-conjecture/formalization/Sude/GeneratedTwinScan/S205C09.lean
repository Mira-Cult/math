import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S205C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20763)) 431095853 431128621 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 431095853 431128621).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20763 431095853 431128621
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20764)) 431128621 431161389 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 431128621 431161389).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20764 431128621 431161389
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20765)) 431161389 431194157 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 431161389 431194157).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20765 431161389 431194157
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20766)) 431194157 431226925 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 431194157 431226925).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20766 431194157 431226925
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 431095853 431161389).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 431095853 ≤ 431128621)
    (by decide : 431128621 ≤ 431161389) block0 block1

theorem join_0_1 : (twinPrimeSegment 431161389 431226925).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 431161389 ≤ 431194157)
    (by decide : 431194157 ≤ 431226925) block2 block3

theorem join_1_0 : (twinPrimeSegment 431095853 431226925).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 431095853 ≤ 431161389)
    (by decide : 431161389 ≤ 431226925) join_0_0 join_0_1

theorem total : (twinPrimeSegment 431095853 431226925).card = 426 := join_1_0

end S205C09
end Sude.GeneratedTwinScan
