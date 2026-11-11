import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S186C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19751)) 390070317 390103085 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 390070317 390103085).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19751 390070317 390103085
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19751)) 390103085 390135853 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 390103085 390135853).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19751 390103085 390135853
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19752)) 390135853 390168621 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 390135853 390168621).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19752 390135853 390168621
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19753)) 390168621 390201389 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 390168621 390201389).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19753 390168621 390201389
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 390070317 390135853).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 390070317 ≤ 390103085)
    (by decide : 390103085 ≤ 390135853) block0 block1

theorem join_0_1 : (twinPrimeSegment 390135853 390201389).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 390135853 ≤ 390168621)
    (by decide : 390168621 ≤ 390201389) block2 block3

theorem join_1_0 : (twinPrimeSegment 390070317 390201389).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 390070317 ≤ 390135853)
    (by decide : 390135853 ≤ 390201389) join_0_0 join_0_1

theorem total : (twinPrimeSegment 390070317 390201389).card = 442 := join_1_0

end S186C00
end Sude.GeneratedTwinScan
