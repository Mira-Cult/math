import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S154C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18026)) 324927533 324960301 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 324927533 324960301).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18026 324927533 324960301
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18027)) 324960301 324993069 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 324960301 324993069).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18027 324960301 324993069
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18028)) 324993069 325025837 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 324993069 325025837).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18028 324993069 325025837
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18029)) 325025837 325058605 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 325025837 325058605).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18029 325025837 325058605
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 324927533 324993069).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 324927533 ≤ 324960301)
    (by decide : 324960301 ≤ 324993069) block0 block1

theorem join_0_1 : (twinPrimeSegment 324993069 325058605).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 324993069 ≤ 325025837)
    (by decide : 325025837 ≤ 325058605) block2 block3

theorem join_1_0 : (twinPrimeSegment 324927533 325058605).card = 473 := by
  simpa using combineTwinPrimeSegments (by decide : 324927533 ≤ 324993069)
    (by decide : 324993069 ≤ 325058605) join_0_0 join_0_1

theorem total : (twinPrimeSegment 324927533 325058605).card = 473 := join_1_0

end S154C15
end Sude.GeneratedTwinScan
