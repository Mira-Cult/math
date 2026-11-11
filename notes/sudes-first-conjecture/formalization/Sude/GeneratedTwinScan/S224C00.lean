import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S224C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21674)) 469762093 469794861 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 469762093 469794861).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21674 469762093 469794861
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21675)) 469794861 469827629 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 469794861 469827629).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21675 469794861 469827629
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21676)) 469827629 469860397 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 469827629 469860397).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21676 469827629 469860397
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21677)) 469860397 469893165 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 469860397 469893165).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21677 469860397 469893165
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 469762093 469827629).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 469762093 ≤ 469794861)
    (by decide : 469794861 ≤ 469827629) block0 block1

theorem join_0_1 : (twinPrimeSegment 469827629 469893165).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 469827629 ≤ 469860397)
    (by decide : 469860397 ≤ 469893165) block2 block3

theorem join_1_0 : (twinPrimeSegment 469762093 469893165).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 469762093 ≤ 469827629)
    (by decide : 469827629 ≤ 469893165) join_0_0 join_0_1

theorem total : (twinPrimeSegment 469762093 469893165).card = 436 := join_1_0

end S224C00
end Sude.GeneratedTwinScan
