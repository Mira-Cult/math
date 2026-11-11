import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S208C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20927)) 437911597 437944365 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 437911597 437944365).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20927 437911597 437944365
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20927)) 437944365 437977133 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 437944365 437977133).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20927 437944365 437977133
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20928)) 437977133 438009901 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 437977133 438009901).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20928 437977133 438009901
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20929)) 438009901 438042669 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 438009901 438042669).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20929 438009901 438042669
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 437911597 437977133).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 437911597 ≤ 437944365)
    (by decide : 437944365 ≤ 437977133) block0 block1

theorem join_0_1 : (twinPrimeSegment 437977133 438042669).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 437977133 ≤ 438009901)
    (by decide : 438009901 ≤ 438042669) block2 block3

theorem join_1_0 : (twinPrimeSegment 437911597 438042669).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 437911597 ≤ 437977133)
    (by decide : 437977133 ≤ 438042669) join_0_0 join_0_1

theorem total : (twinPrimeSegment 437911597 438042669).card = 443 := join_1_0

end S208C13
end Sude.GeneratedTwinScan
