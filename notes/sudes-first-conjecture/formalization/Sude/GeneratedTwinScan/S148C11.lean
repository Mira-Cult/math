import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S148C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17659)) 311820333 311853101 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 311820333 311853101).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17659 311820333 311853101
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17660)) 311853101 311885869 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 311853101 311885869).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17660 311853101 311885869
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17661)) 311885869 311918637 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 311885869 311918637).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17661 311885869 311918637
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17662)) 311918637 311951405 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 311918637 311951405).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17662 311918637 311951405
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 311820333 311885869).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 311820333 ≤ 311853101)
    (by decide : 311853101 ≤ 311885869) block0 block1

theorem join_0_1 : (twinPrimeSegment 311885869 311951405).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 311885869 ≤ 311918637)
    (by decide : 311918637 ≤ 311951405) block2 block3

theorem join_1_0 : (twinPrimeSegment 311820333 311951405).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 311820333 ≤ 311885869)
    (by decide : 311885869 ≤ 311951405) join_0_0 join_0_1

theorem total : (twinPrimeSegment 311820333 311951405).card = 450 := join_1_0

end S148C11
end Sude.GeneratedTwinScan
