import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S225C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21735)) 472383533 472416301 = 97 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 472383533 472416301).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21735 472383533 472416301
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21735)) 472416301 472449069 = 83 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 472416301 472449069).card = 83 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21735 472416301 472449069
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21736)) 472449069 472481837 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 472449069 472481837).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21736 472449069 472481837
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21737)) 472481837 472514605 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 472481837 472514605).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21737 472481837 472514605
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 472383533 472449069).card = 180 := by
  simpa using combineTwinPrimeSegments (by decide : 472383533 ≤ 472416301)
    (by decide : 472416301 ≤ 472449069) block0 block1

theorem join_0_1 : (twinPrimeSegment 472449069 472514605).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 472449069 ≤ 472481837)
    (by decide : 472481837 ≤ 472514605) block2 block3

theorem join_1_0 : (twinPrimeSegment 472383533 472514605).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 472383533 ≤ 472449069)
    (by decide : 472449069 ≤ 472514605) join_0_0 join_0_1

theorem total : (twinPrimeSegment 472383533 472514605).card = 430 := join_1_0

end S225C04
end Sude.GeneratedTwinScan
