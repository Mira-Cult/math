import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S184C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19654)) 386269229 386301997 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 386269229 386301997).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19654 386269229 386301997
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19655)) 386301997 386334765 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 386301997 386334765).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19655 386301997 386334765
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19656)) 386334765 386367533 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 386334765 386367533).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19656 386334765 386367533
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19657)) 386367533 386400301 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 386367533 386400301).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19657 386367533 386400301
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 386269229 386334765).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 386269229 ≤ 386301997)
    (by decide : 386301997 ≤ 386334765) block0 block1

theorem join_0_1 : (twinPrimeSegment 386334765 386400301).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 386334765 ≤ 386367533)
    (by decide : 386367533 ≤ 386400301) block2 block3

theorem join_1_0 : (twinPrimeSegment 386269229 386400301).card = 437 := by
  simpa using combineTwinPrimeSegments (by decide : 386269229 ≤ 386334765)
    (by decide : 386334765 ≤ 386400301) join_0_0 join_0_1

theorem total : (twinPrimeSegment 386269229 386400301).card = 437 := join_1_0

end S184C03
end Sude.GeneratedTwinScan
