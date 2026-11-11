import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S170C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18913)) 357695533 357728301 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 357695533 357728301).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18913 357695533 357728301
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18914)) 357728301 357761069 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 357728301 357761069).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18914 357728301 357761069
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18915)) 357761069 357793837 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 357761069 357793837).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18915 357761069 357793837
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18916)) 357793837 357826605 = 91 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 357793837 357826605).card = 91 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18916 357793837 357826605
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 357695533 357761069).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 357695533 ≤ 357728301)
    (by decide : 357728301 ≤ 357761069) block0 block1

theorem join_0_1 : (twinPrimeSegment 357761069 357826605).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 357761069 ≤ 357793837)
    (by decide : 357793837 ≤ 357826605) block2 block3

theorem join_1_0 : (twinPrimeSegment 357695533 357826605).card = 419 := by
  simpa using combineTwinPrimeSegments (by decide : 357695533 ≤ 357761069)
    (by decide : 357761069 ≤ 357826605) join_0_0 join_0_1

theorem total : (twinPrimeSegment 357695533 357826605).card = 419 := join_1_0

end S170C09
end Sude.GeneratedTwinScan
