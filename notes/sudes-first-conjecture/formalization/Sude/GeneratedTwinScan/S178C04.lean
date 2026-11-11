import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S178C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19335)) 373817389 373850157 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 373817389 373850157).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19335 373817389 373850157
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19336)) 373850157 373882925 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 373850157 373882925).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19336 373850157 373882925
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19336)) 373882925 373915693 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 373882925 373915693).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19336 373882925 373915693
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19337)) 373915693 373948461 = 93 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 373915693 373948461).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19337 373915693 373948461
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 373817389 373882925).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 373817389 ≤ 373850157)
    (by decide : 373850157 ≤ 373882925) block0 block1

theorem join_0_1 : (twinPrimeSegment 373882925 373948461).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 373882925 ≤ 373915693)
    (by decide : 373915693 ≤ 373948461) block2 block3

theorem join_1_0 : (twinPrimeSegment 373817389 373948461).card = 424 := by
  simpa using combineTwinPrimeSegments (by decide : 373817389 ≤ 373882925)
    (by decide : 373882925 ≤ 373948461) join_0_0 join_0_1

theorem total : (twinPrimeSegment 373817389 373948461).card = 424 := join_1_0

end S178C04
end Sude.GeneratedTwinScan
