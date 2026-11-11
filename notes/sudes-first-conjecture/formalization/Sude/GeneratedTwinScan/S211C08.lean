import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S211C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21061)) 443547693 443580461 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 443547693 443580461).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21061 443547693 443580461
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21062)) 443580461 443613229 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 443580461 443613229).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21062 443580461 443613229
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21062)) 443613229 443645997 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 443613229 443645997).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21062 443613229 443645997
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21063)) 443645997 443678765 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 443645997 443678765).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21063 443645997 443678765
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 443547693 443613229).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 443547693 ≤ 443580461)
    (by decide : 443580461 ≤ 443613229) block0 block1

theorem join_0_1 : (twinPrimeSegment 443613229 443678765).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 443613229 ≤ 443645997)
    (by decide : 443645997 ≤ 443678765) block2 block3

theorem join_1_0 : (twinPrimeSegment 443547693 443678765).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 443547693 ≤ 443613229)
    (by decide : 443613229 ≤ 443678765) join_0_0 join_0_1

theorem total : (twinPrimeSegment 443547693 443678765).card = 463 := join_1_0

end S211C08
end Sude.GeneratedTwinScan
