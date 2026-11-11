import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S225C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21729)) 472121389 472154157 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 472121389 472154157).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21729 472121389 472154157
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21729)) 472154157 472186925 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 472154157 472186925).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21729 472154157 472186925
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21730)) 472186925 472219693 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 472186925 472219693).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21730 472186925 472219693
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21731)) 472219693 472252461 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 472219693 472252461).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21731 472219693 472252461
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 472121389 472186925).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 472121389 ≤ 472154157)
    (by decide : 472154157 ≤ 472186925) block0 block1

theorem join_0_1 : (twinPrimeSegment 472186925 472252461).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 472186925 ≤ 472219693)
    (by decide : 472219693 ≤ 472252461) block2 block3

theorem join_1_0 : (twinPrimeSegment 472121389 472252461).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 472121389 ≤ 472186925)
    (by decide : 472186925 ≤ 472252461) join_0_0 join_0_1

theorem total : (twinPrimeSegment 472121389 472252461).card = 435 := join_1_0

end S225C02
end Sude.GeneratedTwinScan
