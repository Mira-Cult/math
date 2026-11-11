import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S233C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22123)) 489422893 489455661 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 489422893 489455661).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22123 489422893 489455661
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22124)) 489455661 489488429 = 97 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 489455661 489488429).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22124 489455661 489488429
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22125)) 489488429 489521197 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 489488429 489521197).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22125 489488429 489521197
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22125)) 489521197 489553965 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 489521197 489553965).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22125 489521197 489553965
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 489422893 489488429).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 489422893 ≤ 489455661)
    (by decide : 489455661 ≤ 489488429) block0 block1

theorem join_0_1 : (twinPrimeSegment 489488429 489553965).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 489488429 ≤ 489521197)
    (by decide : 489521197 ≤ 489553965) block2 block3

theorem join_1_0 : (twinPrimeSegment 489422893 489553965).card = 452 := by
  simpa using combineTwinPrimeSegments (by decide : 489422893 ≤ 489488429)
    (by decide : 489488429 ≤ 489553965) join_0_0 join_0_1

theorem total : (twinPrimeSegment 489422893 489553965).card = 452 := join_1_0

end S233C06
end Sude.GeneratedTwinScan
