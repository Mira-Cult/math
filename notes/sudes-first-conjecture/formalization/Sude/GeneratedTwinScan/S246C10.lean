import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S246C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22742)) 517210157 517242925 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 517210157 517242925).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22742 517210157 517242925
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22743)) 517242925 517275693 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 517242925 517275693).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22743 517242925 517275693
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22744)) 517275693 517308461 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 517275693 517308461).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22744 517275693 517308461
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22745)) 517308461 517341229 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 517308461 517341229).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22745 517308461 517341229
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 517210157 517275693).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 517210157 ≤ 517242925)
    (by decide : 517242925 ≤ 517275693) block0 block1

theorem join_0_1 : (twinPrimeSegment 517275693 517341229).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 517275693 ≤ 517308461)
    (by decide : 517308461 ≤ 517341229) block2 block3

theorem join_1_0 : (twinPrimeSegment 517210157 517341229).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 517210157 ≤ 517275693)
    (by decide : 517275693 ≤ 517341229) join_0_0 join_0_1

theorem total : (twinPrimeSegment 517210157 517341229).card = 432 := join_1_0

end S246C10
end Sude.GeneratedTwinScan
