import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S245C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22699)) 515244077 515276845 = 83 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 515244077 515276845).card = 83 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22699 515244077 515276845
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22700)) 515276845 515309613 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 515276845 515309613).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22700 515276845 515309613
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22701)) 515309613 515342381 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 515309613 515342381).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22701 515309613 515342381
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22701)) 515342381 515375149 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 515342381 515375149).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22701 515342381 515375149
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 515244077 515309613).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 515244077 ≤ 515276845)
    (by decide : 515276845 ≤ 515309613) block0 block1

theorem join_0_1 : (twinPrimeSegment 515309613 515375149).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 515309613 ≤ 515342381)
    (by decide : 515342381 ≤ 515375149) block2 block3

theorem join_1_0 : (twinPrimeSegment 515244077 515375149).card = 427 := by
  simpa using combineTwinPrimeSegments (by decide : 515244077 ≤ 515309613)
    (by decide : 515309613 ≤ 515375149) join_0_0 join_0_1

theorem total : (twinPrimeSegment 515244077 515375149).card = 427 := join_1_0

end S245C11
end Sude.GeneratedTwinScan
