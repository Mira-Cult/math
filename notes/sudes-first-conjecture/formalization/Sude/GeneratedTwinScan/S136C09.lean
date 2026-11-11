import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S136C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16924)) 286392365 286425133 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 286392365 286425133).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16924 286392365 286425133
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16925)) 286425133 286457901 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 286425133 286457901).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16925 286425133 286457901
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16926)) 286457901 286490669 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 286457901 286490669).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16926 286457901 286490669
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16927)) 286490669 286523437 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 286490669 286523437).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16927 286490669 286523437
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 286392365 286457901).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 286392365 ≤ 286425133)
    (by decide : 286425133 ≤ 286457901) block0 block1

theorem join_0_1 : (twinPrimeSegment 286457901 286523437).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 286457901 ≤ 286490669)
    (by decide : 286490669 ≤ 286523437) block2 block3

theorem join_1_0 : (twinPrimeSegment 286392365 286523437).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 286392365 ≤ 286457901)
    (by decide : 286457901 ≤ 286523437) join_0_0 join_0_1

theorem total : (twinPrimeSegment 286392365 286523437).card = 463 := join_1_0

end S136C09
end Sude.GeneratedTwinScan
