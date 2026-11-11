import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S229C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21924)) 480641069 480673837 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 480641069 480673837).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21924 480641069 480673837
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21925)) 480673837 480706605 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 480673837 480706605).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21925 480673837 480706605
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21925)) 480706605 480739373 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 480706605 480739373).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21925 480706605 480739373
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21926)) 480739373 480772141 = 92 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 480739373 480772141).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21926 480739373 480772141
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 480641069 480706605).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 480641069 ≤ 480673837)
    (by decide : 480673837 ≤ 480706605) block0 block1

theorem join_0_1 : (twinPrimeSegment 480706605 480772141).card = 197 := by
  simpa using combineTwinPrimeSegments (by decide : 480706605 ≤ 480739373)
    (by decide : 480739373 ≤ 480772141) block2 block3

theorem join_1_0 : (twinPrimeSegment 480641069 480772141).card = 416 := by
  simpa using combineTwinPrimeSegments (by decide : 480641069 ≤ 480706605)
    (by decide : 480706605 ≤ 480772141) join_0_0 join_0_1

theorem total : (twinPrimeSegment 480641069 480772141).card = 416 := join_1_0

end S229C03
end Sude.GeneratedTwinScan
