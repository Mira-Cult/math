import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S190C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19985)) 399376429 399409197 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 399376429 399409197).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19985 399376429 399409197
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19986)) 399409197 399441965 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 399409197 399441965).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19986 399409197 399441965
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19986)) 399441965 399474733 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 399441965 399474733).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19986 399441965 399474733
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19987)) 399474733 399507501 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 399474733 399507501).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19987 399474733 399507501
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 399376429 399441965).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 399376429 ≤ 399409197)
    (by decide : 399409197 ≤ 399441965) block0 block1

theorem join_0_1 : (twinPrimeSegment 399441965 399507501).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 399441965 ≤ 399474733)
    (by decide : 399474733 ≤ 399507501) block2 block3

theorem join_1_0 : (twinPrimeSegment 399376429 399507501).card = 437 := by
  simpa using combineTwinPrimeSegments (by decide : 399376429 ≤ 399441965)
    (by decide : 399441965 ≤ 399507501) join_0_0 join_0_1

theorem total : (twinPrimeSegment 399376429 399507501).card = 437 := join_1_0

end S190C07
end Sude.GeneratedTwinScan
