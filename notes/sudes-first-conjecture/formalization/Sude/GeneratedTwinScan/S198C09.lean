import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S198C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20407)) 416415789 416448557 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 416415789 416448557).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20407 416415789 416448557
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20407)) 416448557 416481325 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 416448557 416481325).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20407 416448557 416481325
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20408)) 416481325 416514093 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 416481325 416514093).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20408 416481325 416514093
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20409)) 416514093 416546861 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 416514093 416546861).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20409 416514093 416546861
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 416415789 416481325).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 416415789 ≤ 416448557)
    (by decide : 416448557 ≤ 416481325) block0 block1

theorem join_0_1 : (twinPrimeSegment 416481325 416546861).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 416481325 ≤ 416514093)
    (by decide : 416514093 ≤ 416546861) block2 block3

theorem join_1_0 : (twinPrimeSegment 416415789 416546861).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 416415789 ≤ 416481325)
    (by decide : 416481325 ≤ 416546861) join_0_0 join_0_1

theorem total : (twinPrimeSegment 416415789 416546861).card = 464 := join_1_0

end S198C09
end Sude.GeneratedTwinScan
