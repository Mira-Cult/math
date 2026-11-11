import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S119C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15806)) 249823277 249856045 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 249823277 249856045).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15806 249823277 249856045
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15807)) 249856045 249888813 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 249856045 249888813).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15807 249856045 249888813
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15808)) 249888813 249921581 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 249888813 249921581).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15808 249888813 249921581
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15809)) 249921581 249954349 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 249921581 249954349).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15809 249921581 249954349
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 249823277 249888813).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 249823277 ≤ 249856045)
    (by decide : 249856045 ≤ 249888813) block0 block1

theorem join_0_1 : (twinPrimeSegment 249888813 249954349).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 249888813 ≤ 249921581)
    (by decide : 249921581 ≤ 249954349) block2 block3

theorem join_1_0 : (twinPrimeSegment 249823277 249954349).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 249823277 ≤ 249888813)
    (by decide : 249888813 ≤ 249954349) join_0_0 join_0_1

theorem total : (twinPrimeSegment 249823277 249954349).card = 447 := join_1_0

end S119C02
end Sude.GeneratedTwinScan
