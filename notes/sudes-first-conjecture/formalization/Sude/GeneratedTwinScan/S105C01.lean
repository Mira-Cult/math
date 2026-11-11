import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S105C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14844)) 220332077 220364845 = 137 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 220332077 220364845).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14844 220332077 220364845
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14845)) 220364845 220397613 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 220364845 220397613).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14845 220364845 220397613
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14846)) 220397613 220430381 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 220397613 220430381).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14846 220397613 220430381
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14848)) 220430381 220463149 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 220430381 220463149).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14848 220430381 220463149
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 220332077 220397613).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 220332077 ≤ 220364845)
    (by decide : 220364845 ≤ 220397613) block0 block1

theorem join_0_1 : (twinPrimeSegment 220397613 220463149).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 220397613 ≤ 220430381)
    (by decide : 220430381 ≤ 220463149) block2 block3

theorem join_1_0 : (twinPrimeSegment 220332077 220463149).card = 500 := by
  simpa using combineTwinPrimeSegments (by decide : 220332077 ≤ 220397613)
    (by decide : 220397613 ≤ 220463149) join_0_0 join_0_1

theorem total : (twinPrimeSegment 220332077 220463149).card = 500 := join_1_0

end S105C01
end Sude.GeneratedTwinScan
