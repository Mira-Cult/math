import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S130C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16528)) 273154093 273186861 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 273154093 273186861).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16528 273154093 273186861
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16529)) 273186861 273219629 = 86 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 273186861 273219629).card = 86 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16529 273186861 273219629
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16530)) 273219629 273252397 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 273219629 273252397).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16530 273219629 273252397
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16531)) 273252397 273285165 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 273252397 273285165).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16531 273252397 273285165
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 273154093 273219629).card = 199 := by
  simpa using combineTwinPrimeSegments (by decide : 273154093 ≤ 273186861)
    (by decide : 273186861 ≤ 273219629) block0 block1

theorem join_0_1 : (twinPrimeSegment 273219629 273285165).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 273219629 ≤ 273252397)
    (by decide : 273252397 ≤ 273285165) block2 block3

theorem join_1_0 : (twinPrimeSegment 273154093 273285165).card = 414 := by
  simpa using combineTwinPrimeSegments (by decide : 273154093 ≤ 273219629)
    (by decide : 273219629 ≤ 273285165) join_0_0 join_0_1

theorem total : (twinPrimeSegment 273154093 273285165).card = 414 := join_1_0

end S130C04
end Sude.GeneratedTwinScan
