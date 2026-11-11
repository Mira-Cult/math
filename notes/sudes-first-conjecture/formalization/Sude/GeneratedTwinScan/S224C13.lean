import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S224C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21714)) 471466029 471498797 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 471466029 471498797).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21714 471466029 471498797
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21714)) 471498797 471531565 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 471498797 471531565).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21714 471498797 471531565
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21715)) 471531565 471564333 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 471531565 471564333).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21715 471531565 471564333
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21716)) 471564333 471597101 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 471564333 471597101).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21716 471564333 471597101
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 471466029 471531565).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 471466029 ≤ 471498797)
    (by decide : 471498797 ≤ 471531565) block0 block1

theorem join_0_1 : (twinPrimeSegment 471531565 471597101).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 471531565 ≤ 471564333)
    (by decide : 471564333 ≤ 471597101) block2 block3

theorem join_1_0 : (twinPrimeSegment 471466029 471597101).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 471466029 ≤ 471531565)
    (by decide : 471531565 ≤ 471597101) join_0_0 join_0_1

theorem total : (twinPrimeSegment 471466029 471597101).card = 454 := join_1_0

end S224C13
end Sude.GeneratedTwinScan
