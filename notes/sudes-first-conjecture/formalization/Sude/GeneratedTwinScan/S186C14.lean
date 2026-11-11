import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S186C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19797)) 391905325 391938093 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 391905325 391938093).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19797 391905325 391938093
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19798)) 391938093 391970861 = 97 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 391938093 391970861).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19798 391938093 391970861
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19799)) 391970861 392003629 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 391970861 392003629).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19799 391970861 392003629
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19799)) 392003629 392036397 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 392003629 392036397).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19799 392003629 392036397
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 391905325 391970861).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 391905325 ≤ 391938093)
    (by decide : 391938093 ≤ 391970861) block0 block1

theorem join_0_1 : (twinPrimeSegment 391970861 392036397).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 391970861 ≤ 392003629)
    (by decide : 392003629 ≤ 392036397) block2 block3

theorem join_1_0 : (twinPrimeSegment 391905325 392036397).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 391905325 ≤ 391970861)
    (by decide : 391970861 ≤ 392036397) join_0_0 join_0_1

theorem total : (twinPrimeSegment 391905325 392036397).card = 443 := join_1_0

end S186C14
end Sude.GeneratedTwinScan
