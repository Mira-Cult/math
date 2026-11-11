import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S175C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19178)) 367788077 367820845 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 367788077 367820845).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19178 367788077 367820845
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19179)) 367820845 367853613 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 367820845 367853613).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19179 367820845 367853613
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19180)) 367853613 367886381 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 367853613 367886381).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19180 367853613 367886381
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19181)) 367886381 367919149 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 367886381 367919149).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19181 367886381 367919149
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 367788077 367853613).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 367788077 ≤ 367820845)
    (by decide : 367820845 ≤ 367853613) block0 block1

theorem join_0_1 : (twinPrimeSegment 367853613 367919149).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 367853613 ≤ 367886381)
    (by decide : 367886381 ≤ 367919149) block2 block3

theorem join_1_0 : (twinPrimeSegment 367788077 367919149).card = 433 := by
  simpa using combineTwinPrimeSegments (by decide : 367788077 ≤ 367853613)
    (by decide : 367853613 ≤ 367919149) join_0_0 join_0_1

theorem total : (twinPrimeSegment 367788077 367919149).card = 433 := join_1_0

end S175C06
end Sude.GeneratedTwinScan
