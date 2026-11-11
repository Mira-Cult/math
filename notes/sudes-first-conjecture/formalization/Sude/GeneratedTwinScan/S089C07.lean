import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S089C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13696)) 187564077 187596845 = 95 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 187564077 187596845).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13696 187564077 187596845
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13697)) 187596845 187629613 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 187596845 187629613).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13697 187596845 187629613
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13698)) 187629613 187662381 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 187629613 187662381).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13698 187629613 187662381
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13700)) 187662381 187695149 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 187662381 187695149).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13700 187662381 187695149
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 187564077 187629613).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 187564077 ≤ 187596845)
    (by decide : 187596845 ≤ 187629613) block0 block1

theorem join_0_1 : (twinPrimeSegment 187629613 187695149).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 187629613 ≤ 187662381)
    (by decide : 187662381 ≤ 187695149) block2 block3

theorem join_1_0 : (twinPrimeSegment 187564077 187695149).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 187564077 ≤ 187629613)
    (by decide : 187629613 ≤ 187695149) join_0_0 join_0_1

theorem total : (twinPrimeSegment 187564077 187695149).card = 439 := join_1_0

end S089C07
end Sude.GeneratedTwinScan
