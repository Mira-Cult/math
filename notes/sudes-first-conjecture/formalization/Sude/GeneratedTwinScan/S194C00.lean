import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S194C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20171)) 406847533 406880301 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 406847533 406880301).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20171 406847533 406880301
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20172)) 406880301 406913069 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 406880301 406913069).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20172 406880301 406913069
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20172)) 406913069 406945837 = 91 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 406913069 406945837).card = 91 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20172 406913069 406945837
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20173)) 406945837 406978605 = 143 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 406945837 406978605).card = 143 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20173 406945837 406978605
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 406847533 406913069).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 406847533 ≤ 406880301)
    (by decide : 406880301 ≤ 406913069) block0 block1

theorem join_0_1 : (twinPrimeSegment 406913069 406978605).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 406913069 ≤ 406945837)
    (by decide : 406945837 ≤ 406978605) block2 block3

theorem join_1_0 : (twinPrimeSegment 406847533 406978605).card = 473 := by
  simpa using combineTwinPrimeSegments (by decide : 406847533 ≤ 406913069)
    (by decide : 406913069 ≤ 406978605) join_0_0 join_0_1

theorem total : (twinPrimeSegment 406847533 406978605).card = 473 := join_1_0

end S194C00
end Sude.GeneratedTwinScan
