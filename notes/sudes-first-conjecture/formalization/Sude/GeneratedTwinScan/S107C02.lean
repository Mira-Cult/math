import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S107C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14989)) 224657453 224690221 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 224657453 224690221).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14989 224657453 224690221
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14990)) 224690221 224722989 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 224690221 224722989).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14990 224690221 224722989
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14991)) 224722989 224755757 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 224722989 224755757).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14991 224722989 224755757
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14992)) 224755757 224788525 = 86 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 224755757 224788525).card = 86 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14992 224755757 224788525
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 224657453 224722989).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 224657453 ≤ 224690221)
    (by decide : 224690221 ≤ 224722989) block0 block1

theorem join_0_1 : (twinPrimeSegment 224722989 224788525).card = 193 := by
  simpa using combineTwinPrimeSegments (by decide : 224722989 ≤ 224755757)
    (by decide : 224755757 ≤ 224788525) block2 block3

theorem join_1_0 : (twinPrimeSegment 224657453 224788525).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 224657453 ≤ 224722989)
    (by decide : 224722989 ≤ 224788525) join_0_0 join_0_1

theorem total : (twinPrimeSegment 224657453 224788525).card = 432 := join_1_0

end S107C02
end Sude.GeneratedTwinScan
