import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S205C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20769)) 431357997 431390765 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 431357997 431390765).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20769 431357997 431390765
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20770)) 431390765 431423533 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 431390765 431423533).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20770 431390765 431423533
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20771)) 431423533 431456301 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 431423533 431456301).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20771 431423533 431456301
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20772)) 431456301 431489069 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 431456301 431489069).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20772 431456301 431489069
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 431357997 431423533).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 431357997 ≤ 431390765)
    (by decide : 431390765 ≤ 431423533) block0 block1

theorem join_0_1 : (twinPrimeSegment 431423533 431489069).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 431423533 ≤ 431456301)
    (by decide : 431456301 ≤ 431489069) block2 block3

theorem join_1_0 : (twinPrimeSegment 431357997 431489069).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 431357997 ≤ 431423533)
    (by decide : 431423533 ≤ 431489069) join_0_0 join_0_1

theorem total : (twinPrimeSegment 431357997 431489069).card = 435 := join_1_0

end S205C11
end Sude.GeneratedTwinScan
