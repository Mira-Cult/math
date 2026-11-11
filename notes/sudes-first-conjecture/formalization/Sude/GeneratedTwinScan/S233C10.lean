import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S233C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22135)) 489947181 489979949 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 489947181 489979949).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22135 489947181 489979949
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22136)) 489979949 490012717 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 489979949 490012717).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22136 489979949 490012717
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22136)) 490012717 490045485 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 490012717 490045485).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22136 490012717 490045485
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22137)) 490045485 490078253 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 490045485 490078253).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22137 490045485 490078253
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 489947181 490012717).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 489947181 ≤ 489979949)
    (by decide : 489979949 ≤ 490012717) block0 block1

theorem join_0_1 : (twinPrimeSegment 490012717 490078253).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 490012717 ≤ 490045485)
    (by decide : 490045485 ≤ 490078253) block2 block3

theorem join_1_0 : (twinPrimeSegment 489947181 490078253).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 489947181 ≤ 490012717)
    (by decide : 490012717 ≤ 490078253) join_0_0 join_0_1

theorem total : (twinPrimeSegment 489947181 490078253).card = 442 := join_1_0

end S233C10
end Sude.GeneratedTwinScan
