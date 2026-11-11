import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S109C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15163)) 229900333 229933101 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 229900333 229933101).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15163 229900333 229933101
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15164)) 229933101 229965869 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 229933101 229965869).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15164 229933101 229965869
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15165)) 229965869 229998637 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 229965869 229998637).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15165 229965869 229998637
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15166)) 229998637 230031405 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 229998637 230031405).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15166 229998637 230031405
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 229900333 229965869).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 229900333 ≤ 229933101)
    (by decide : 229933101 ≤ 229965869) block0 block1

theorem join_0_1 : (twinPrimeSegment 229965869 230031405).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 229965869 ≤ 229998637)
    (by decide : 229998637 ≤ 230031405) block2 block3

theorem join_1_0 : (twinPrimeSegment 229900333 230031405).card = 452 := by
  simpa using combineTwinPrimeSegments (by decide : 229900333 ≤ 229965869)
    (by decide : 229965869 ≤ 230031405) join_0_0 join_0_1

theorem total : (twinPrimeSegment 229900333 230031405).card = 452 := join_1_0

end S109C10
end Sude.GeneratedTwinScan
