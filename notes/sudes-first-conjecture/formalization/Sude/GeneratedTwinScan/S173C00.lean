import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S173C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19048)) 362807341 362840109 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 362807341 362840109).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19048 362807341 362840109
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19049)) 362840109 362872877 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 362840109 362872877).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19049 362840109 362872877
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19050)) 362872877 362905645 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 362872877 362905645).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19050 362872877 362905645
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19050)) 362905645 362938413 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 362905645 362938413).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19050 362905645 362938413
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 362807341 362872877).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 362807341 ≤ 362840109)
    (by decide : 362840109 ≤ 362872877) block0 block1

theorem join_0_1 : (twinPrimeSegment 362872877 362938413).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 362872877 ≤ 362905645)
    (by decide : 362905645 ≤ 362938413) block2 block3

theorem join_1_0 : (twinPrimeSegment 362807341 362938413).card = 494 := by
  simpa using combineTwinPrimeSegments (by decide : 362807341 ≤ 362872877)
    (by decide : 362872877 ≤ 362938413) join_0_0 join_0_1

theorem total : (twinPrimeSegment 362807341 362938413).card = 494 := join_1_0

end S173C00
end Sude.GeneratedTwinScan
