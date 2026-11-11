import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S138C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17062)) 291110957 291143725 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 291110957 291143725).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17062 291110957 291143725
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17063)) 291143725 291176493 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 291143725 291176493).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17063 291143725 291176493
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17064)) 291176493 291209261 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 291176493 291209261).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17064 291176493 291209261
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17065)) 291209261 291242029 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 291209261 291242029).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17065 291209261 291242029
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 291110957 291176493).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 291110957 ≤ 291143725)
    (by decide : 291143725 ≤ 291176493) block0 block1

theorem join_0_1 : (twinPrimeSegment 291176493 291242029).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 291176493 ≤ 291209261)
    (by decide : 291209261 ≤ 291242029) block2 block3

theorem join_1_0 : (twinPrimeSegment 291110957 291242029).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 291110957 ≤ 291176493)
    (by decide : 291176493 ≤ 291242029) join_0_0 join_0_1

theorem total : (twinPrimeSegment 291110957 291242029).card = 463 := join_1_0

end S138C13
end Sude.GeneratedTwinScan
