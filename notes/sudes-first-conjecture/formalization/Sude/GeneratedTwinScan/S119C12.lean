import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S119C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15848)) 251133997 251166765 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 251133997 251166765).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15848 251133997 251166765
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15849)) 251166765 251199533 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 251166765 251199533).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15849 251166765 251199533
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15850)) 251199533 251232301 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 251199533 251232301).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15850 251199533 251232301
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15851)) 251232301 251265069 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 251232301 251265069).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15851 251232301 251265069
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 251133997 251199533).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 251133997 ≤ 251166765)
    (by decide : 251166765 ≤ 251199533) block0 block1

theorem join_0_1 : (twinPrimeSegment 251199533 251265069).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 251199533 ≤ 251232301)
    (by decide : 251232301 ≤ 251265069) block2 block3

theorem join_1_0 : (twinPrimeSegment 251133997 251265069).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 251133997 ≤ 251199533)
    (by decide : 251199533 ≤ 251265069) join_0_0 join_0_1

theorem total : (twinPrimeSegment 251133997 251265069).card = 442 := join_1_0

end S119C12
end Sude.GeneratedTwinScan
