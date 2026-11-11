import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S242C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22549)) 508428333 508461101 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 508428333 508461101).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22549 508428333 508461101
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22549)) 508461101 508493869 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 508461101 508493869).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22549 508461101 508493869
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22550)) 508493869 508526637 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 508493869 508526637).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22550 508493869 508526637
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22551)) 508526637 508559405 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 508526637 508559405).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22551 508526637 508559405
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 508428333 508493869).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 508428333 ≤ 508461101)
    (by decide : 508461101 ≤ 508493869) block0 block1

theorem join_0_1 : (twinPrimeSegment 508493869 508559405).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 508493869 ≤ 508526637)
    (by decide : 508526637 ≤ 508559405) block2 block3

theorem join_1_0 : (twinPrimeSegment 508428333 508559405).card = 433 := by
  simpa using combineTwinPrimeSegments (by decide : 508428333 ≤ 508493869)
    (by decide : 508493869 ≤ 508559405) join_0_0 join_0_1

theorem total : (twinPrimeSegment 508428333 508559405).card = 433 := join_1_0

end S242C07
end Sude.GeneratedTwinScan
