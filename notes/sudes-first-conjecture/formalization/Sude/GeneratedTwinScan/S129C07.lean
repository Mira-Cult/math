import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S129C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16476)) 271450157 271482925 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 271450157 271482925).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16476 271450157 271482925
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16477)) 271482925 271515693 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 271482925 271515693).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16477 271482925 271515693
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16478)) 271515693 271548461 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 271515693 271548461).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16478 271515693 271548461
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16479)) 271548461 271581229 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 271548461 271581229).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16479 271548461 271581229
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 271450157 271515693).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 271450157 ≤ 271482925)
    (by decide : 271482925 ≤ 271515693) block0 block1

theorem join_0_1 : (twinPrimeSegment 271515693 271581229).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 271515693 ≤ 271548461)
    (by decide : 271548461 ≤ 271581229) block2 block3

theorem join_1_0 : (twinPrimeSegment 271450157 271581229).card = 433 := by
  simpa using combineTwinPrimeSegments (by decide : 271450157 ≤ 271515693)
    (by decide : 271515693 ≤ 271581229) join_0_0 join_0_1

theorem total : (twinPrimeSegment 271450157 271581229).card = 433 := join_1_0

end S129C07
end Sude.GeneratedTwinScan
