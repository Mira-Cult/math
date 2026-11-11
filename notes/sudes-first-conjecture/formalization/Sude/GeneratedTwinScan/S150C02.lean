import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S150C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17744)) 314834989 314867757 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 314834989 314867757).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17744 314834989 314867757
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17745)) 314867757 314900525 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 314867757 314900525).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17745 314867757 314900525
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17746)) 314900525 314933293 = 96 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 314900525 314933293).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17746 314900525 314933293
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17747)) 314933293 314966061 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 314933293 314966061).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17747 314933293 314966061
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 314834989 314900525).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 314834989 ≤ 314867757)
    (by decide : 314867757 ≤ 314900525) block0 block1

theorem join_0_1 : (twinPrimeSegment 314900525 314966061).card = 196 := by
  simpa using combineTwinPrimeSegments (by decide : 314900525 ≤ 314933293)
    (by decide : 314933293 ≤ 314966061) block2 block3

theorem join_1_0 : (twinPrimeSegment 314834989 314966061).card = 437 := by
  simpa using combineTwinPrimeSegments (by decide : 314834989 ≤ 314900525)
    (by decide : 314900525 ≤ 314966061) join_0_0 join_0_1

theorem total : (twinPrimeSegment 314834989 314966061).card = 437 := join_1_0

end S150C02
end Sude.GeneratedTwinScan
