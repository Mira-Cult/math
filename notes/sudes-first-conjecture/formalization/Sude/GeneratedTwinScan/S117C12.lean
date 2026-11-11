import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S117C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15715)) 246939693 246972461 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 246939693 246972461).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15715 246939693 246972461
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15716)) 246972461 247005229 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 246972461 247005229).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15716 246972461 247005229
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15717)) 247005229 247037997 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 247005229 247037997).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15717 247005229 247037997
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15718)) 247037997 247070765 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 247037997 247070765).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15718 247037997 247070765
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 246939693 247005229).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 246939693 ≤ 246972461)
    (by decide : 246972461 ≤ 247005229) block0 block1

theorem join_0_1 : (twinPrimeSegment 247005229 247070765).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 247005229 ≤ 247037997)
    (by decide : 247037997 ≤ 247070765) block2 block3

theorem join_1_0 : (twinPrimeSegment 246939693 247070765).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 246939693 ≤ 247005229)
    (by decide : 247005229 ≤ 247070765) join_0_0 join_0_1

theorem total : (twinPrimeSegment 246939693 247070765).card = 454 := join_1_0

end S117C12
end Sude.GeneratedTwinScan
