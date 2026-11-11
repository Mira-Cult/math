import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S213C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21142)) 446955565 446988333 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 446955565 446988333).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21142 446955565 446988333
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21142)) 446988333 447021101 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 446988333 447021101).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21142 446988333 447021101
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21143)) 447021101 447053869 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 447021101 447053869).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21143 447021101 447053869
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21144)) 447053869 447086637 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 447053869 447086637).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21144 447053869 447086637
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 446955565 447021101).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 446955565 ≤ 446988333)
    (by decide : 446988333 ≤ 447021101) block0 block1

theorem join_0_1 : (twinPrimeSegment 447021101 447086637).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 447021101 ≤ 447053869)
    (by decide : 447053869 ≤ 447086637) block2 block3

theorem join_1_0 : (twinPrimeSegment 446955565 447086637).card = 417 := by
  simpa using combineTwinPrimeSegments (by decide : 446955565 ≤ 447021101)
    (by decide : 447021101 ≤ 447086637) join_0_0 join_0_1

theorem total : (twinPrimeSegment 446955565 447086637).card = 417 := join_1_0

end S213C02
end Sude.GeneratedTwinScan
