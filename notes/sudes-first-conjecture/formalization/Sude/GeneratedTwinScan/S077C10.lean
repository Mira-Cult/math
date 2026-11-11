import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S077C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12760)) 162791469 162824237 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 162791469 162824237).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12760 162791469 162824237
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12761)) 162824237 162857005 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 162824237 162857005).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12761 162824237 162857005
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12762)) 162857005 162889773 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 162857005 162889773).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12762 162857005 162889773
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12764)) 162889773 162922541 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 162889773 162922541).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12764 162889773 162922541
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 162791469 162857005).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 162791469 ≤ 162824237)
    (by decide : 162824237 ≤ 162857005) block0 block1

theorem join_0_1 : (twinPrimeSegment 162857005 162922541).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 162857005 ≤ 162889773)
    (by decide : 162889773 ≤ 162922541) block2 block3

theorem join_1_0 : (twinPrimeSegment 162791469 162922541).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 162791469 ≤ 162857005)
    (by decide : 162857005 ≤ 162922541) join_0_0 join_0_1

theorem total : (twinPrimeSegment 162791469 162922541).card = 454 := join_1_0

end S077C10
end Sude.GeneratedTwinScan
