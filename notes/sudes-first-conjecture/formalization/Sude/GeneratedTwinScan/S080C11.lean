import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S080C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13009)) 169213997 169246765 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 169213997 169246765).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13009 169213997 169246765
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13010)) 169246765 169279533 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 169246765 169279533).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13010 169246765 169279533
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13012)) 169279533 169312301 = 141 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 169279533 169312301).card = 141 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13012 169279533 169312301
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13013)) 169312301 169345069 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 169312301 169345069).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13013 169312301 169345069
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 169213997 169279533).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 169213997 ≤ 169246765)
    (by decide : 169246765 ≤ 169279533) block0 block1

theorem join_0_1 : (twinPrimeSegment 169279533 169345069).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 169279533 ≤ 169312301)
    (by decide : 169312301 ≤ 169345069) block2 block3

theorem join_1_0 : (twinPrimeSegment 169213997 169345069).card = 512 := by
  simpa using combineTwinPrimeSegments (by decide : 169213997 ≤ 169279533)
    (by decide : 169279533 ≤ 169345069) join_0_0 join_0_1

theorem total : (twinPrimeSegment 169213997 169345069).card = 512 := join_1_0

end S080C11
end Sude.GeneratedTwinScan
